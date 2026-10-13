(ns rainbow.math.finite.policy-iteration
  "Finite exact-rational policy improvement and one composed iteration step."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- improve [state action actions current score]
  (function/app
   (function/const* 'policy/nnrat-improve [U V])
   state action actions current score))

(def equivalent-to-at-most-spec
  {:name 'nnrat/equivalent-to-at-most
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat] ['same (equivalent 'left 'right)]]
    (at-most 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat] ['same (equivalent 'left 'right)]]
    (function/app
     (function/const* 'nnrat/at-most-from-cross [])
     'left 'right
     (function/app
      (function/const* 'nat/at-most-rewrite-right [])
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'left)
       (function/app (function/const* 'nnrat/denominator []) 'right))
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'left)
       (function/app (function/const* 'nnrat/denominator []) 'right))
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'right)
       (function/app (function/const* 'nnrat/denominator []) 'left))
      'same
      (function/app
       (function/const* 'nat/at-most-reflexive [])
       (function/app
        (function/const* 'nat/multiply [])
        (function/app (function/const* 'nnrat/numerator []) 'left)
        (function/app (function/const* 'nnrat/denominator []) 'right))))))})

(def at-most-respects-equivalence-spec
  {:name 'nnrat/at-most-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left nnrat] ['equivalent-left nnrat]
     ['right nnrat] ['equivalent-right nnrat]
     ['same-left (equivalent 'left 'equivalent-left)]
     ['same-right (equivalent 'right 'equivalent-right)]
     ['ordered (at-most 'equivalent-left 'equivalent-right)]]
    (at-most 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['equivalent-left nnrat]
     ['right nnrat] ['equivalent-right nnrat]
     ['same-left (equivalent 'left 'equivalent-left)]
     ['same-right (equivalent 'right 'equivalent-right)]
     ['ordered (at-most 'equivalent-left 'equivalent-right)]]
    (function/app
     (function/const* 'nnrat/at-most-transitive [])
     'left 'equivalent-left 'right
     (function/app (function/const* 'nnrat/equivalent-to-at-most [])
                   'left 'equivalent-left 'same-left)
     (function/app
      (function/const* 'nnrat/at-most-transitive [])
      'equivalent-left 'equivalent-right 'right 'ordered
      (function/app
       (function/const* 'nnrat/equivalent-to-at-most [])
       'equivalent-right 'right
       (function/app (function/const* 'nnrat/equivalent-symmetric [])
                     'right 'equivalent-right 'same-right)))))})

(def improve-spec
  {:name 'policy/nnrat-improve
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]]
    (function/arrow 'S 'A))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)] ['state 'S]]
    (function/app
     (function/const* 'decision/finite-nnrat-argmax [V])
     'A 'actions (function/app 'current 'state)
     (function/app 'score 'state)))})

(def iteration-step-spec
  {:name 'policy/nnrat-iteration-step
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['evaluate (function/arrow (function/arrow 'S 'A)
                                (function/arrow 'S nnrat))]
     ['action-score
      (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]]
    (function/arrow 'S 'A))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['evaluate (function/arrow (function/arrow 'S 'A)
                                (function/arrow 'S nnrat))]
     ['action-score
      (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]]
    (improve 'S 'A 'actions 'current
             (function/app 'action-score
                           (function/app 'evaluate 'current))))})

(def definition-specs [improve-spec iteration-step-spec])

(def improve-admissible-spec
  {:name 'policy/nnrat-improve-is-admissible
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (function/app 'current 'state)))]
     ['state 'S]]
    (source-membership V 'A 'actions
                       (function/app
                        (improve 'S 'A 'actions 'current 'score) 'state)))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (function/app 'current 'state)))]
     ['state 'S]]
    (function/app
     (function/const* 'decision/finite-nnrat-argmax-is-member [V])
     'A 'actions (function/app 'current 'state)
     (function/app 'score 'state)
     (function/app 'current-admissible 'state)))})

(def improve-dominates-spec
  {:name 'policy/nnrat-improve-dominates
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['state 'S] ['candidate 'A]
     ['member (source-membership V 'A 'actions 'candidate)]]
    (at-most
     (function/app 'score 'state 'candidate)
     (function/app 'score 'state
                   (function/app
                    (improve 'S 'A 'actions 'current 'score) 'state))))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['state 'S] ['candidate 'A]
     ['member (source-membership V 'A 'actions 'candidate)]]
    (function/app
     (function/const* 'decision/finite-nnrat-argmax-dominates [V])
     'A 'actions (function/app 'current 'state)
     (function/app 'score 'state) 'candidate 'member))})

(def iteration-step-unfold-spec
  (let [evaluated (function/app 'evaluate 'current)
        score (function/app 'action-score evaluated)
        step
        (function/app
         (function/const* 'policy/nnrat-iteration-step [U V])
         'S 'A 'actions 'current 'evaluate 'action-score)
        improved (improve 'S 'A 'actions 'current score)]
    {:name 'policy/nnrat-iteration-step-unfold
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['current (function/arrow 'S 'A)]
       ['evaluate (function/arrow (function/arrow 'S 'A)
                                  (function/arrow 'S nnrat))]
       ['action-score
        (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['state 'S]]
      (function/equality data-v 'A
                         (function/app step 'state)
                         (function/app improved 'state)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['current (function/arrow 'S 'A)]
       ['evaluate (function/arrow (function/arrow 'S 'A)
                                  (function/arrow 'S nnrat))]
       ['action-score
        (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['state 'S]]
      (function/app (function/const* 'equality/reflexive [data-v])
                    'A (function/app improved 'state)))}))

(def improvement-model-transfer-spec
  (let [selected
        (function/app (improve 'S 'A 'actions 'current 'left-score) 'state)
        left-dominance
        (function/app
         (function/const* 'policy/nnrat-improve-dominates [U V])
         'S 'A 'actions 'current 'left-score 'state 'candidate 'member)]
    {:name 'policy/nnrat-improvement-model-transfer
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['current (function/arrow 'S 'A)]
       ['left-score (function/arrow 'S 'A nnrat)]
       ['right-score (function/arrow 'S 'A nnrat)]
       ['same-score
        (function/forall
         [['state 'S] ['action 'A]]
         (equivalent (function/app 'left-score 'state 'action)
                     (function/app 'right-score 'state 'action)))]
       ['state 'S] ['candidate 'A]
       ['member (source-membership V 'A 'actions 'candidate)]]
      (at-most (function/app 'right-score 'state 'candidate)
               (function/app 'right-score 'state selected)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['current (function/arrow 'S 'A)]
       ['left-score (function/arrow 'S 'A nnrat)]
       ['right-score (function/arrow 'S 'A nnrat)]
       ['same-score
        (function/forall
         [['state 'S] ['action 'A]]
         (equivalent (function/app 'left-score 'state 'action)
                     (function/app 'right-score 'state 'action)))]
       ['state 'S] ['candidate 'A]
       ['member (source-membership V 'A 'actions 'candidate)]]
      (function/app
       (function/const* 'nnrat/at-most-respects-equivalence [])
       (function/app 'right-score 'state 'candidate)
       (function/app 'left-score 'state 'candidate)
       (function/app 'right-score 'state selected)
       (function/app 'left-score 'state selected)
       (function/app
        (function/const* 'nnrat/equivalent-symmetric [])
        (function/app 'left-score 'state 'candidate)
        (function/app 'right-score 'state 'candidate)
        (function/app 'same-score 'state 'candidate))
       (function/app
        (function/const* 'nnrat/equivalent-symmetric [])
        (function/app 'left-score 'state selected)
        (function/app 'right-score 'state selected)
        (function/app 'same-score 'state selected))
       left-dominance))}))

(def improvement-state-transfer-spec
  {:name 'policy/nnrat-improvement-state-transfer
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (function/app 'current 'state)))]
     ['state 'S]]
    (proposition/conjunction
     (source-membership
      V 'A 'actions
      (function/app (improve 'S 'A 'actions 'current 'score) 'state))
     (function/forall
      [['candidate 'A]
       ['member (source-membership V 'A 'actions 'candidate)]]
      (at-most
       (function/app 'score 'state 'candidate)
       (function/app 'score 'state
                     (function/app
                      (improve 'S 'A 'actions 'current 'score) 'state))))))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (function/app 'current 'state)))]
     ['state 'S]]
    (function/app
     (function/const* 'proposition/conjoin [])
     (source-membership
      V 'A 'actions
      (function/app (improve 'S 'A 'actions 'current 'score) 'state))
     (function/forall
      [['candidate 'A]
       ['member (source-membership V 'A 'actions 'candidate)]]
      (at-most
       (function/app 'score 'state 'candidate)
       (function/app 'score 'state
                     (function/app
                      (improve 'S 'A 'actions 'current 'score) 'state))))
     (function/app
      (function/const* 'policy/nnrat-improve-is-admissible [U V])
      'S 'A 'actions 'current 'score 'current-admissible 'state)
     (function/lam
      [['candidate 'A]
       ['member (source-membership V 'A 'actions 'candidate)]]
      (function/app
       (function/const* 'policy/nnrat-improve-dominates [U V])
       'S 'A 'actions 'current 'score 'state 'candidate 'member))))})

(def theorem-specs
  [equivalent-to-at-most-spec at-most-respects-equivalence-spec
   improve-admissible-spec improve-dominates-spec iteration-step-unfold-spec
   improvement-model-transfer-spec improvement-state-transfer-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite policy-iteration expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-policy-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite policy-iteration declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.policy-iteration))
(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
