(ns rainbow.math.finite.policy-improvement
  "Policy-iteration monotonic improvement (Q-score level): the greedy-improved
  policy's action-score dominates the current policy's at every state.

    policy/nnrat-improve-dominates-current :
      for admissible current policy and any score (Q-function),
        score(s, current s) <= score(s, improve(actions,current,score) s)  for all s.

  I.e. improving a policy never lowers any state's chosen-action score -- the
  monotonic-improvement guarantee that makes policy iteration climb toward the
  optimum.  It is policy/nnrat-improve-dominates instantiated at the admissible
  candidate = current(s): the argmax that defines the improved policy scores at
  least as high as the incumbent action.

  With a fixed-policy value V^pi consistent in Q-form (V^pi(s) = score(s,
  current s)) this reads V^pi(s) <= score(s, improved s) = T_{pi'} V^pi(s), the
  entry point of the policy-improvement value dominance V^pi <= V^{pi'}.
  Native and axiom-free; chains finite-policy-iteration on the d21 checkpoint."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.finite.policy-iteration :as pi]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level]) element source value))
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- improve [S A actions current score]
  (function/app (function/const* 'policy/nnrat-improve [U V]) S A actions current score))
(defn- improve-dominates [S A actions current score state candidate member]
  (function/app (function/const* 'policy/nnrat-improve-dominates [U V])
                S A actions current score state candidate member))

(def improve-dominates-current-spec
  {:name 'policy/nnrat-improve-dominates-current
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'current 's)))]
     ['state 'S]]
    (at-most (function/app 'score 'state (function/app 'current 'state))
             (function/app 'score 'state
                           (function/app (improve 'S 'A 'actions 'current 'score) 'state))))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['current (function/arrow 'S 'A)]
     ['score (function/arrow 'S 'A nnrat)]
     ['current-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'current 's)))]
     ['state 'S]]
    (improve-dominates 'S 'A 'actions 'current 'score 'state
                       (function/app 'current 'state)
                       (function/app 'current-admissible 'state)))})

(def definition-specs [])
(def theorem-specs [improve-dominates-current-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Policy-improvement expression failed elaboration"
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
          :rainbow/dependencies (into (term/constants type) (term/constants value))
          :rainbow/provenance {:origin :native :producer :finite-policy-improvement}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Policy-improvement declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.policy-iteration])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.policy-improvement))
(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec] [(:name spec)
                         (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec] [(:name spec)
                         (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
