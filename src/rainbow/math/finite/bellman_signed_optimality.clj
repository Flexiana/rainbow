(ns rainbow.math.finite.bellman-signed-optimality
  "Generic finite Bellman optimality over exact signed-rational action scores.

  The operator is parameterized by an action-backup function.  Its greedy
  action is executable over a runtime-length finite carrier; the certificates
  prove admissibility, dominance of every admissible action and policy, an
  explicit unfold equation, and preservation of one- and two-sided additive
  epsilon bounds supplied pointwise for the backup.

  This module does not yet prove that a transition-weighted signed Bellman
  action backup supplies those bounds.  Native, kernel-checked, and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.signed-argmax-nonexpansive :as argmax]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- greedy-action [state action actions fallback backup value current]
  (app (function/const* 'value/signed-greedy-action [U V])
       state action actions fallback backup value current))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- symmetric [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       signed left right same))
(defn- substitution [left right same motive proof]
  (app (function/const* 'equality/substitution [type-level])
       signed left right same motive proof))

(def greedy-action-spec
  {:name 'value/signed-greedy-action
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)]]
    (function/arrow 'S 'A))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)] ['state 'S]]
    (app
     (function/const* 'decision/finite-signed-argmax [V])
     'A 'actions (app 'fallback 'state)
     (app 'backup 'value 'state)))})

(def optimality-step-spec
  {:name 'value/signed-optimality-step
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)]]
    (function/arrow 'S signed))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)] ['state 'S]]
    (app
     'backup 'value 'state
     (greedy-action 'S 'A 'actions 'fallback 'backup 'value 'state)))})

(def greedy-action-admissible-spec
  (let [selected
        (greedy-action 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/signed-greedy-action-is-admissible
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['value (function/arrow 'S signed)] ['state 'S]]
      (source-membership V 'A 'actions selected))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['value (function/arrow 'S signed)] ['state 'S]]
      (app
       (function/const* 'decision/finite-signed-argmax-is-member [V])
       'A 'actions (app 'fallback 'state)
       (app 'backup 'value 'state)
       (app 'fallback-admissible 'state)))}))

(def optimality-dominates-spec
  (let [optimum
        (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/signed-optimality-step-dominates
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['value (function/arrow 'S signed)] ['state 'S]
       ['candidate 'A]
       ['candidate-member (source-membership V 'A 'actions 'candidate)]]
      (at-most (app 'backup 'value 'state 'candidate) optimum))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['value (function/arrow 'S signed)] ['state 'S]
       ['candidate 'A]
       ['candidate-member (source-membership V 'A 'actions 'candidate)]]
      (app
       (function/const* 'decision/finite-signed-argmax-dominates [V])
       'A 'actions (app 'fallback 'state)
       (app 'backup 'value 'state) 'candidate 'candidate-member))}))

(def optimality-step-unfold-spec
  (let [selected
        (greedy-action 'S 'A 'actions 'fallback 'backup 'value 'state)
        optimum
        (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/signed-optimality-step-unfold
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['value (function/arrow 'S signed)] ['state 'S]]
      (function/equality
       type-level signed optimum
       (app 'backup 'value 'state selected)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['value (function/arrow 'S signed)] ['state 'S]]
      (app (function/const* 'equality/reflexive [type-level])
           signed optimum))}))

(def optimality-dominates-policy-spec
  {:name 'value/signed-optimality-step-dominates-policy
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall
       [['current 'S]]
       (source-membership V 'A 'actions (app 'policy 'current)))]
     ['state 'S]]
    (at-most
     (app 'backup 'value 'state (app 'policy 'state))
     (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['value (function/arrow 'S signed)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall
       [['current 'S]]
       (source-membership V 'A 'actions (app 'policy 'current)))]
     ['state 'S]]
    (app
     (function/const* 'value/signed-optimality-step-dominates [U V])
     'S 'A 'actions 'fallback 'backup 'value 'state
     (app 'policy 'state) (app 'policy-admissible 'state)))})

(def optimality-step-additive-upper-bound-spec
  (let [left-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'left-value 'state)
        right-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'right-value 'state)]
    {:name 'value/signed-optimality-step-additive-upper-bound
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed] ['state 'S]
       ['pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'left-value 'state 'action)
                  (add (app 'backup 'right-value 'state 'action) 'epsilon)))]]
      (at-most left-step (add right-step 'epsilon)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed] ['state 'S]
       ['pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'left-value 'state 'action)
                  (add (app 'backup 'right-value 'state 'action) 'epsilon)))]]
      (let [left-score
            (function/lam
             [['action 'A]] (app 'backup 'left-value 'state 'action))
            right-score
            (function/lam
             [['action 'A]] (app 'backup 'right-value 'state 'action))
            fallback-action (app 'fallback 'state)
            left-selected
            (app (function/const* 'decision/finite-signed-argmax [V])
                 'A 'actions fallback-action left-score)
            right-selected
            (app (function/const* 'decision/finite-signed-argmax [V])
                 'A 'actions fallback-action right-score)
            left-selected-value (app left-score left-selected)
            right-selected-value (app right-score right-selected)
            maximum-bound
            (app
             (function/const*
              'decision/finite-signed-argmax-additive-upper-bound [V])
             'A 'actions fallback-action
             (app 'fallback-admissible 'state)
             left-score right-score 'epsilon 'pointwise)
            left-unfold
            (app
             (function/const* 'value/signed-optimality-step-unfold [U V])
             'S 'A 'actions 'fallback 'backup 'left-value 'state)
            right-unfold
            (app
             (function/const* 'value/signed-optimality-step-unfold [U V])
             'S 'A 'actions 'fallback 'backup 'right-value 'state)
            expose-left
            (substitution
             left-selected-value left-step
             (symmetric left-step left-selected-value left-unfold)
             (function/lam
              [['candidate signed]]
              (at-most 'candidate (add right-selected-value 'epsilon)))
             maximum-bound)]
        (substitution
         right-selected-value right-step
         (symmetric right-step right-selected-value right-unfold)
         (function/lam
          [['candidate signed]]
          (at-most left-step (add 'candidate 'epsilon)))
         expose-left)))}))

(def optimality-step-additively-nonexpansive-spec
  (let [left-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'left-value 'state)
        right-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'right-value 'state)
        left-to-right (at-most left-step (add right-step 'epsilon))
        right-to-left (at-most right-step (add left-step 'epsilon))]
    {:name 'value/signed-optimality-step-additively-nonexpansive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed] ['state 'S]
       ['left-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'left-value 'state 'action)
                  (add (app 'backup 'right-value 'state 'action) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'right-value 'state 'action)
                  (add (app 'backup 'left-value 'state 'action) 'epsilon)))]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions (app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S signed) 'S 'A signed)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed] ['state 'S]
       ['left-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'left-value 'state 'action)
                  (add (app 'backup 'right-value 'state 'action) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (app 'backup 'right-value 'state 'action)
                  (add (app 'backup 'left-value 'state 'action) 'epsilon)))]]
      (app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (app
        (function/const*
         'value/signed-optimality-step-additive-upper-bound [U V])
        'S 'A 'actions 'fallback 'fallback-admissible 'backup
        'left-value 'right-value 'epsilon 'state 'left-pointwise)
       (app
        (function/const*
         'value/signed-optimality-step-additive-upper-bound [U V])
        'S 'A 'actions 'fallback 'fallback-admissible 'backup
        'right-value 'left-value 'epsilon 'state 'right-pointwise)))}))

(def definition-specs [greedy-action-spec optimality-step-spec])
(def theorem-specs
  [greedy-action-admissible-spec
   optimality-dominates-spec
   optimality-step-unfold-spec
   optimality-dominates-policy-spec
   optimality-step-additive-upper-bound-spec
   optimality-step-additively-nonexpansive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.signed-argmax-nonexpansive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-optimality (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-optimality))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
