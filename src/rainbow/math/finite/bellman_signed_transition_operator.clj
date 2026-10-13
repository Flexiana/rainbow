(ns rainbow.math.finite.bellman-signed-transition-operator
  "Named concrete signed Bellman operator over ordinary nnrat transitions.

  A stable name for the concrete operator prevents downstream proofs from
  repeatedly expanding embedded transitions, signed expectations, action
  backups and finite argmax.  A separate low-arity operator iterator keeps its
  successor law independent of that expansion.  Opaque successor and
  contraction theorems form the compact proof boundary.  This remains a
  mathematical interface, not an executable solver.  Native, kernel-checked,
  and axiom-free on D63."
  (:require [rainbow.math.finite.bellman-signed-approximate-optimality
             :as approximate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def type-v [:sort [:succ V]])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- harmonic-radius [index]
  (from-nnrat (app (function/const* 'nnrat/harmonic []) index)))
(defn- general-harmonic-radius [ap gp steps]
  (from-nnrat
   (app (function/const* 'nnrat/general-harmonic []) ap gp steps)))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- optimality-step
  [actions fallback backup value state]
  (app (function/const* 'value/signed-optimality-step [U V])
       'S 'A actions fallback backup value state))
(defn- generic-iterate
  [actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       'S 'A actions fallback backup steps initial))

(defn- model-binders []
  (let [value-function (function/arrow 'S signed)]
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['actions (exact-finset-of V 'A)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A signed)]
     ['discount nnrat]
     ['fallback (function/arrow 'S 'A)]]))

(defn- concrete-objects []
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat 'discount)
        backup
        (function/lam
         [['value value-function] ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward embedded-discount
              'value 'state 'action))
        raw-operator
        (function/lam
         [['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step 'actions 'fallback backup 'value 'state)))
        named-operator
        (apply app
               (function/const*
                'value/nnrat-transition-signed-optimality-operator [U V])
               (map first (model-binders)))
        named-iterate
        (fn [steps initial]
          (app (function/const* 'value/signed-operator-iterate [U])
               'S named-operator steps initial))]
    {:value-function value-function
     :embedded-transition embedded-transition
     :embedded-discount embedded-discount
     :backup backup :raw-operator raw-operator
     :named-operator named-operator :named-iterate named-iterate}))

(def signed-transition-optimality-operator-spec
  (let [{:keys [value-function raw-operator]} (concrete-objects)]
    {:name 'value/nnrat-transition-signed-optimality-operator
     :kind :definition
     :universes ['u 'v]
     :transparency :reducible
     :type
     (function/forall
      (model-binders)
      (function/arrow value-function value-function))
     :value
     (function/lam (model-binders) raw-operator)}))

(def signed-transition-optimality-iterate-spec
  (let [value-function (function/arrow 'S signed)
        step
        (function/lam
         [['ignored-step nat] ['previous value-function]]
         (app 'operator 'previous))]
    {:name 'value/signed-operator-iterate
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['S type-u] ['operator (function/arrow value-function value-function)]]
      (function/arrow nat value-function value-function))
     :value
     (function/lam
      [['S type-u] ['operator (function/arrow value-function value-function)]
       ['steps nat] ['initial value-function]]
      (app
       (function/const* 'data/Nat.rec [data-u])
       (function/lam [['ignored nat]] value-function)
       'initial step 'steps))}))

(def signed-transition-optimality-operator-unfold-spec
  (let [{:keys [value-function raw-operator named-operator]}
        (concrete-objects)]
    {:name 'value/nnrat-transition-signed-optimality-operator-unfold
     :universes ['u 'v]
     :type
     (function/forall
      (into (model-binders)
            [['value value-function] ['state 'S]])
      (veq (app named-operator 'value 'state)
           (app raw-operator 'value 'state)))
     :value
     (function/lam
      (into (model-binders)
            [['value value-function] ['state 'S]])
      (app (function/const* 'signed/equivalent-reflexive [])
           (app named-operator 'value 'state)))}))

(def signed-transition-optimality-iterate-successor-spec
  (let [value-function (function/arrow 'S signed)
        iterate
        (fn [steps initial]
          (app (function/const* 'value/signed-operator-iterate [U])
               'S 'operator steps initial))
        current (iterate 'steps 'initial)
        next (iterate (succ 'steps) 'initial)
        step
        (function/lam
         [['ignored-step nat] ['previous value-function]]
         (app 'operator 'previous))]
    {:name 'value/signed-operator-iterate-successor
     :universes ['u]
     :type
     (function/forall
      [['S type-u] ['operator (function/arrow value-function value-function)]
       ['steps nat] ['initial value-function]]
      (function/equality
       data-u value-function next (app 'operator current)))
     :value
     (function/lam
      [['S type-u] ['operator (function/arrow value-function value-function)]
       ['steps nat] ['initial value-function]]
      (app (function/const* 'nat/recursor-successor-constant [U])
           value-function 'initial step 'steps))}))

(defn- close-at [left right epsilon state]
  (proposition/conjunction
   (sle (app left state) (sadd (app right state) epsilon))
   (sle (app right state) (sadd (app left state) epsilon))))

(def signed-operator-iterate-successor-equivalent-spec
  (let [value-function (function/arrow 'S signed)
        iterate
        (fn [steps]
          (app (function/const* 'value/signed-operator-iterate [U])
               'S 'operator steps 'initial))
        current (iterate 'steps)
        next (iterate (succ 'steps))
        image (app 'operator current)]
    {:name 'value/signed-operator-iterate-successor-equivalent
     :universes ['u]
     :type
     (function/forall
      [['S type-u] ['operator (function/arrow value-function value-function)]
       ['steps nat] ['initial value-function] ['state 'S]]
      (veq (app next 'state) (app image 'state)))
     :value
     (function/lam
      [['S type-u] ['operator (function/arrow value-function value-function)]
       ['steps nat] ['initial value-function] ['state 'S]]
      (app
       (function/const* 'equality/substitution [data-u])
       value-function next image
       (app (function/const* 'value/signed-operator-iterate-successor [U])
            'S 'operator 'steps 'initial)
       (function/lam
        [['candidate value-function]]
        (veq (app next 'state) (app 'candidate 'state)))
       (app (function/const* 'signed/equivalent-reflexive [])
            (app next 'state))))}))

(def signed-operator-successive-iterate-radius-spec
  (let [value-function (function/arrow 'S signed)
        iterate
        (fn [steps]
          (app (function/const* 'value/signed-operator-iterate [U])
               'S 'operator steps 'initial))
        sequence (function/lam [['steps nat]] (iterate 'steps))]
    {:name 'value/signed-operator-successive-iterate-additive-radius
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['discount signed]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial (app 'operator 'initial)
                   'initial-error 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (app 'operator 'left) (app 'operator 'right)
                    (smul 'discount 'epsilon) 'state)))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (iterate 'steps) (iterate (succ 'steps))
                 (error-radius 'discount 'initial-error 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['discount signed]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial (app 'operator 'initial)
                   'initial-error 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (app 'operator 'left) (app 'operator 'right)
                    (smul 'discount 'epsilon) 'state)))]]
      (app
       (function/const*
        'value/signed-abstract-successive-iterate-additive-radius [U])
       'S 'operator sequence 'discount 'initial-error
       (function/lam
        [['steps nat] ['state 'S]]
        (app
         (function/const*
          'value/signed-operator-iterate-successor-equivalent [U])
         'S 'operator 'steps 'initial 'state))
       'initial-close 'advance))}))

(def signed-contractive-operator-approximate-fixed-point-general-rate-spec
  (let [value-function (function/arrow 'S signed)
        gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        discount (from-nnrat gamma)
        iterate
        (fn [steps]
          (app (function/const* 'value/signed-operator-iterate [U])
               'S 'operator steps 'initial))
        sequence (function/lam [['steps nat]] (iterate 'steps))
        radius
        (function/lam
         [['steps nat]] (error-radius discount 'initial-error 'steps))
        modulus
        (function/lam [['index nat]] (nmul (succ 'ap) 'index))
        candidate (app sequence (app modulus 'index))
        binders
        [['ap nat] ['gp nat]
         ['S type-u]
         ['operator (function/arrow value-function value-function)]
         ['initial value-function] ['initial-error signed]
         ['initial-error-nonnegative (sle signed-zero 'initial-error)]
         ['initial-bound
          (sle 'initial-error
               (general-harmonic-radius 'ap 'gp nat-zero))]
         ['initial-close
          (function/forall
           [['state 'S]]
           (close-at 'initial (app 'operator 'initial)
                     'initial-error 'state))]
         ['advance
          (function/forall
           [['left value-function] ['right value-function]
            ['epsilon signed]
            ['close
             (function/forall
              [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
           (function/forall
            [['state 'S]]
            (close-at (app 'operator 'left) (app 'operator 'right)
                      (smul discount 'epsilon) 'state)))]]]
    {:name
     'value/signed-contractive-operator-approximate-fixed-point-general-rate
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['index nat] ['state 'S]]
       (close-at candidate (app 'operator candidate)
                 (harmonic-radius 'index) 'state)))
     :value
     (function/lam
      binders
      (function/lam
       [['index nat] ['state 'S]]
       (app
        (function/const*
         'value/signed-rate-certificate-approximate-fixed-point [U])
        'S 'operator sequence radius modulus
        (function/lam
         [['steps nat] ['selected-state 'S]]
         (app
          (function/const*
           'value/signed-operator-iterate-successor-equivalent [U])
          'S 'operator 'steps 'initial 'selected-state))
        (app
         (function/const*
          'value/signed-operator-successive-iterate-additive-radius [U])
         'S 'operator discount 'initial 'initial-error
         'initial-close 'advance)
        (app
         (function/const*
          'analysis/signed-vi-error-radius-rate-null-general [])
         'ap 'gp 'initial-error
         'initial-error-nonnegative 'initial-bound)
        'index 'state)))}))

(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def signed-transition-optimality-operator-contractive-spec
  (let [{:keys [value-function named-operator embedded-discount]}
        (concrete-objects)]
    {:name 'value/nnrat-transition-signed-optimality-operator-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      (into
       (model-binders)
       [['fallback-admissible
         (function/forall
          [['state 'S]]
          (source-membership V 'A 'actions (app 'fallback 'state)))]
        ['normalized
         (function/forall
          [['state 'S] ['action 'A]]
          (req (nnrat-total-mass
                'S 'states (app 'transition 'state 'action))
               (function/const* 'nnrat/one [])))]
        ['left value-function] ['right value-function]
        ['epsilon signed]
        ['close
         (function/forall
          [['state 'S]] (close-at 'left 'right 'epsilon 'state))]])
      (function/forall
       [['state 'S]]
       (close-at (app named-operator 'left)
                 (app named-operator 'right)
                 (smul embedded-discount 'epsilon) 'state)))
     :value
     (function/lam
      (into
       (model-binders)
       [['fallback-admissible
         (function/forall
          [['state 'S]]
          (source-membership V 'A 'actions (app 'fallback 'state)))]
        ['normalized
         (function/forall
          [['state 'S] ['action 'A]]
          (req (nnrat-total-mass
                'S 'states (app 'transition 'state 'action))
               (function/const* 'nnrat/one [])))]
        ['left value-function] ['right value-function]
        ['epsilon signed]
        ['close
         (function/forall
          [['state 'S]] (close-at 'left 'right 'epsilon 'state))]
        ['state 'S]])
      (app
       (function/const*
        'value/nnrat-transition-signed-optimality-step-additively-contractive
        [U V])
       'S 'A 'states 'actions 'transition 'reward 'discount
       'fallback 'fallback-admissible 'normalized
       'left 'right 'epsilon
       (function/lam
        [['selected-state 'S]]
        (let [both (app 'close 'selected-state)
              left-bound
              (sle (app 'left 'selected-state)
                   (sadd (app 'right 'selected-state) 'epsilon))
              right-bound
              (sle (app 'right 'selected-state)
                   (sadd (app 'left 'selected-state) 'epsilon))]
          (left-conjunct left-bound right-bound both)))
       (function/lam
        [['selected-state 'S]]
        (let [both (app 'close 'selected-state)
              left-bound
              (sle (app 'left 'selected-state)
                   (sadd (app 'right 'selected-state) 'epsilon))
              right-bound
              (sle (app 'right 'selected-state)
                   (sadd (app 'left 'selected-state) 'epsilon))]
          (right-conjunct left-bound right-bound both)))
       'state))}))

(def definition-specs
  [signed-transition-optimality-operator-spec
   signed-transition-optimality-iterate-spec])
(def theorem-specs
  [signed-transition-optimality-operator-unfold-spec
   signed-transition-optimality-iterate-successor-spec
   signed-operator-iterate-successor-equivalent-spec
   signed-operator-successive-iterate-radius-spec
   signed-contractive-operator-approximate-fixed-point-general-rate-spec
   signed-transition-optimality-operator-contractive-spec])

(defn extend-environment [env]
  (-> env
      approximate/extend-environment
      (support/extend-with
       :finite-bellman-signed-transition-operator
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
