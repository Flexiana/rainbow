(ns rainbow.math.finite.bellman-optimality
  "Bellman optimality, operator level: the optimal (greedy / max-over-actions)
  Bellman backup dominates every fixed-policy backup.

    value/nnrat-optimality-step-dominates-policy :
      for any admissible policy pi (pi : S -> A with pi s in actions for all s),
        backup(V, s, pi s)  <=  optimality-step(backup, V, s)

  i.e. T_pi V <= T* V pointwise -- the foundational operator inequality of Bellman
  optimality: no single-step policy backup can exceed the optimal (argmax) backup.
  It lifts the per-ACTION argmax dominance (value/nnrat-optimality-step-dominates,
  quantified over candidate actions) to a per-POLICY statement by instantiating
  the candidate at the policy's chosen action pi(s), whose admissibility is the
  policy-admissibility hypothesis.

  Combined with value/nnrat-optimality-step-unfold (optimality-step = backup at
  the greedy action), this says the greedy policy attains T* and dominates every
  other policy's one-step backup.  The remaining step to full value-function
  Bellman optimality (V^pi <= V* for the fixed-point values) is the monotone
  iteration of T* to its fixed point (needs T*-monotonicity + convergence).
  Native and axiom-free; chains finite-value-iteration on the d21 checkpoint."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.finite.value-iteration :as fvi]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
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
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- optimality-step [S A actions fallback backup value state]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                S A actions fallback backup value state))
(defn- optimality-dominates [S A actions fallback backup value state candidate member]
  (function/app (function/const* 'value/nnrat-optimality-step-dominates [U V])
                S A actions fallback backup value state candidate member))
(defn- greedy-action [S A actions fallback backup value state]
  (function/app (function/const* 'value/nnrat-greedy-action [U V])
                S A actions fallback backup value state))
(defn- optimality-unfold [S A actions fallback backup value state]
  (function/app (function/const* 'value/nnrat-optimality-step-unfold [U V])
                S A actions fallback backup value state))
(defn- eq-nnrat [a b] (function/equality type-level nnrat a b))
(defn- substitution [x y h P px]
  (function/app (function/const* 'equality/substitution [type-level]) nnrat x y h P px))

(def optimality-dominates-policy-spec
  {:name 'value/nnrat-optimality-step-dominates-policy
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'policy 's)))]
     ['state 'S]]
    (at-most (function/app 'backup 'value 'state (function/app 'policy 'state))
             (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'policy 's)))]
     ['state 'S]]
    (optimality-dominates 'S 'A 'actions 'fallback 'backup 'value 'state
                          (function/app 'policy 'state)
                          (function/app 'policy-admissible 'state)))})

;; greedy is the one-step-optimal policy: its backup dominates every policy's
(def greedy-dominates-policy-spec
  {:name 'value/nnrat-greedy-dominates-policy
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'policy 's)))]
     ['state 'S]]
    (at-most (function/app 'backup 'value 'state (function/app 'policy 'state))
             (function/app 'backup 'value 'state
                           (greedy-action 'S 'A 'actions 'fallback 'backup 'value 'state))))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]
     ['policy (function/arrow 'S 'A)]
     ['policy-admissible
      (function/forall [['s 'S]]
                       (source-membership V 'A 'actions (function/app 'policy 's)))]
     ['state 'S]]
    (let [pol-backup (function/app 'backup 'value 'state (function/app 'policy 'state))
          opt (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)
          greedy-backup (function/app 'backup 'value 'state
                                      (greedy-action 'S 'A 'actions 'fallback 'backup 'value 'state))
          dom (optimality-dominates 'S 'A 'actions 'fallback 'backup 'value 'state
                                    (function/app 'policy 'state)
                                    (function/app 'policy-admissible 'state))  ; pol-backup <= opt
          unfold (optimality-unfold 'S 'A 'actions 'fallback 'backup 'value 'state) ; opt = greedy-backup
          motive (function/lam [['z nnrat]] (at-most pol-backup 'z))]
      ;; transport (pol-backup <= opt) along (opt = greedy-backup)
      (substitution opt greedy-backup unfold motive dom)))})

(def definition-specs [])
(def theorem-specs [optimality-dominates-policy-spec greedy-dominates-policy-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Bellman-optimality expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :finite-bellman-optimality}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Bellman-optimality declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.value-iteration])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman-optimality))
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
