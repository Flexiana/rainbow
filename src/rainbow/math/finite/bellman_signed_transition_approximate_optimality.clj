(ns rainbow.math.finite.bellman-signed-transition-approximate-optimality
  "Constructive approximate optimality for normalized finite signed MDPs.

  The witness is the actual generic iterate of the named concrete Bellman
  optimality operator.  For discount gamma=(a+1)/(a+g+2), an initial residual
  bounded by the corresponding general-harmonic radius yields, at horizon
  (a+1)*k, a pointwise Bellman residual at most 1/(k+1).  A finite-sup theorem
  turns that whole-carrier result into a scalar certificate over the supplied
  finite state source.  No exact fixed point or choice principle is assumed.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-approximate-optimality
             :as approximate]
            [rainbow.math.finite.bellman-signed-transition-operator
             :as transition-operator]
            [rainbow.math.finite.signed-approximate-fixed-point-sup
             :as sup-bridge]
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
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
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
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- harmonic-radius [index]
  (from-nnrat (app (function/const* 'nnrat/harmonic []) index)))
(defn- general-harmonic-radius [ap gp steps]
  (from-nnrat
   (app (function/const* 'nnrat/general-harmonic []) ap gp steps)))
(defn- close-at [left right epsilon state]
  (proposition/conjunction
   (sle (app left state) (sadd (app right state) epsilon))
   (sle (app right state) (sadd (app left state) epsilon))))
(defn- finite-sup-distance [source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [U])
       'S source left right))

(declare named-operator)

(defn- model-binders [discount]
  (let [value-function (function/arrow 'S signed)]
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['actions (exact-finset-of V 'A)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A signed)]
     ['fallback (function/arrow 'S 'A)]
     ['fallback-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (app 'fallback 'state)))]
     ['normalized
      (function/forall
       [['state 'S] ['action 'A]]
       (req (nnrat-total-mass
             'S 'states (app 'transition 'state 'action))
            (function/const* 'nnrat/one [])))]
     ['initial value-function] ['initial-error signed]
     ['initial-close
      (function/forall
       [['state 'S]]
       (close-at
        'initial
        (app (named-operator discount) 'initial)
        'initial-error 'state))]]))

(defn- named-operator [discount]
  (app
   (function/const*
    'value/nnrat-transition-signed-optimality-operator [U V])
   'S 'A 'states 'actions 'transition 'reward discount 'fallback))

(defn- operator-iterate [operator steps initial]
  (app (function/const* 'value/signed-operator-iterate [U])
       'S operator steps initial))

(defn- sequence-at [operator steps]
  (operator-iterate operator steps 'initial))

(defn- successor-equivalence [value-function operator steps state]
  (let [current (sequence-at operator steps)
        next (sequence-at operator (succ steps))
        image (app operator current)
        successor-equality
        (app (function/const* 'value/signed-operator-iterate-successor [U])
             'S operator steps 'initial)]
    (app
     (function/const* 'equality/substitution [data-u])
     value-function next image successor-equality
     (function/lam
      [['candidate value-function]]
      (veq (app next state) (app 'candidate state)))
     (app (function/const* 'signed/equivalent-reflexive [])
          (app next state)))))

(defn- contraction-proof [discount value-function]
  (function/lam
   [['left value-function] ['right value-function]
    ['epsilon signed]
    ['close
     (function/forall
      [['state 'S]] (close-at 'left 'right 'epsilon 'state))]
    ['state 'S]]
   (app
    (function/const*
     'value/nnrat-transition-signed-optimality-operator-additively-contractive
     [U V])
    'S 'A 'states 'actions 'transition 'reward discount 'fallback
    'fallback-admissible 'normalized
    'left 'right 'epsilon 'close 'state)))

(def transition-successive-iterate-radius-spec
  (let [value-function (function/arrow 'S signed)
        operator (named-operator 'discount)
        sequence (function/lam [['steps nat]] (sequence-at operator 'steps))]
    {:name
     'value/nnrat-transition-signed-optimality-successive-iterate-additive-radius
     :universes ['u 'v]
     :type
     (function/forall
      (into
       [['discount nnrat]]
       (model-binders 'discount))
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at
        (sequence-at operator 'steps)
        (sequence-at operator (succ 'steps))
        (error-radius (from-nnrat 'discount) 'initial-error 'steps)
        'state)))
     :value
     (function/lam
      (into
       [['discount nnrat]]
       (model-binders 'discount))
      (app
       (function/const*
        'value/signed-operator-successive-iterate-additive-radius [U])
       'S operator (from-nnrat 'discount) 'initial 'initial-error
       'initial-close
       (contraction-proof 'discount value-function)))}))

(defn- general-binders []
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))]
    (into
     [['ap nat] ['gp nat]]
     (concat
      (model-binders gamma)
      [['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (general-harmonic-radius 'ap 'gp nat-zero))]]))))

(defn- general-objects []
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        operator (named-operator gamma)
        sequence (function/lam [['steps nat]] (sequence-at operator 'steps))
        radius
        (function/lam
         [['steps nat]]
         (error-radius (from-nnrat gamma) 'initial-error 'steps))
        modulus
        (function/lam [['index nat]] (nmul (succ 'ap) 'index))]
    {:gamma gamma :operator operator :sequence sequence
     :radius radius :modulus modulus}))

(def transition-approximate-fixed-point-general-rate-spec
  (let [value-function (function/arrow 'S signed)
        {:keys [gamma operator sequence radius modulus]} (general-objects)
        horizon (app modulus 'index)
        candidate (app sequence horizon)]
    {:name
     'value/nnrat-transition-signed-optimality-approximate-fixed-point-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (general-binders)
      (function/forall
       [['index nat] ['state 'S]]
       (close-at candidate (app operator candidate)
                 (harmonic-radius 'index) 'state)))
     :value
     (function/lam
      (general-binders)
      (function/lam
       [['index nat] ['state 'S]]
       (app
        (function/const*
         'value/signed-contractive-operator-approximate-fixed-point-general-rate
         [U])
        'ap 'gp 'S operator 'initial 'initial-error
        'initial-error-nonnegative 'initial-bound 'initial-close
        (contraction-proof gamma value-function)
        'index 'state)))}))

(def transition-approximate-fixed-point-exists-general-rate-spec
  (let [value-function (function/arrow 'S signed)
        {:keys [operator sequence modulus]} (general-objects)
        candidate (app sequence (app modulus 'index))
        predicate
        (function/lam
         [['candidate value-function]]
         (function/forall
          [['state 'S]]
          (close-at 'candidate (app operator 'candidate)
                    (harmonic-radius 'index) 'state)))]
    {:name
     'value/nnrat-transition-signed-optimality-approximate-fixed-point-exists-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (into (general-binders) [['index nat]])
      (proposition/existence data-u value-function predicate))
     :value
     (function/lam
      (into (general-binders) [['index nat]])
      (app
       (function/const* 'proposition/witness [data-u])
       value-function predicate candidate
       (function/lam
        [['state 'S]]
        (app
         (function/const*
          'value/nnrat-transition-signed-optimality-approximate-fixed-point-general-rate
          [U V])
         'ap 'gp 'S 'A 'states 'actions 'transition 'reward 'fallback
         'fallback-admissible 'normalized
         'initial 'initial-error 'initial-close
         'initial-error-nonnegative 'initial-bound
         'index 'state))))}))

(def transition-approximate-fixed-point-sup-general-rate-spec
  (let [{:keys [operator sequence modulus]} (general-objects)
        candidate (app sequence (app modulus 'index))
        tolerance-nnrat (app (function/const* 'nnrat/harmonic []) 'index)
        tolerance (from-nnrat tolerance-nnrat)]
    {:name
     'value/nnrat-transition-signed-optimality-approximate-fixed-point-sup-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (into (general-binders) [['index nat]])
      (sle (finite-sup-distance 'states candidate (app operator candidate))
           tolerance))
     :value
     (function/lam
      (into (general-binders) [['index nat]])
      (app
       (function/const*
        'value/signed-pointwise-approximate-fixed-point-sup-certificate [U])
       'S 'states operator candidate tolerance
       (app
        (function/const* 'signed/from-nnrat-at-most [])
        nnrat-zero tolerance-nnrat
        (app (function/const* 'nnrat/zero-at-most []) tolerance-nnrat))
       (function/lam
        [['state 'S]]
        (app
         (function/const*
          'value/nnrat-transition-signed-optimality-approximate-fixed-point-general-rate
          [U V])
         'ap 'gp 'S 'A 'states 'actions 'transition 'reward 'fallback
         'fallback-admissible 'normalized
         'initial 'initial-error 'initial-close
         'initial-error-nonnegative 'initial-bound
         'index 'state))))}))

(def definition-specs [])
(def theorem-specs
  [transition-successive-iterate-radius-spec
   transition-approximate-fixed-point-general-rate-spec
   transition-approximate-fixed-point-exists-general-rate-spec
   transition-approximate-fixed-point-sup-general-rate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-approximate-optimality rainbow.math.finite.bellman-signed-transition-operator rainbow.math.finite.signed-approximate-fixed-point-sup])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-transition-approximate-optimality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-transition-approximate-optimality))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
