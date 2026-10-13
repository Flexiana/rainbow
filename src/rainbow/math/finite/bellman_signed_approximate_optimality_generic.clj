(ns rainbow.math.finite.bellman-signed-approximate-optimality-generic
  "Approximate fixed points for a certified finite signed Bellman operator.

  This specializes the abstract successive-iterate proof to Rainbow's actual
  runtime finite-argmax Bellman iterate while retaining the operator's
  two-sided additive contraction as an explicit certificate.  Existing
  normalized-transition Bellman theorems produce that certificate; keeping it
  opaque avoids re-expanding transition sums and argmax during every induction
  step.

  For gamma=(a+1)/(a+g+2), the iterate at horizon (a+1)*k is pointwise within
  1/(k+1) of its next Bellman image and is packaged as an existential witness.
  No exact fixed point is assumed or constructed.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-approximate-optimality
             :as abstract]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
             :as general-convergence]
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
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- optimality-step [actions fallback backup value state]
  (app (function/const* 'value/signed-optimality-step [U V])
       'S 'A actions fallback backup value state))
(defn- iterate-value [actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       'S 'A actions fallback backup steps initial))
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
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))

(defn- bellman-objects []
  (let [value-function (function/arrow 'S signed)
        operator
        (function/lam
         [['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step 'actions 'fallback 'backup 'value 'state)))
        sequence
        (function/lam
         [['steps nat]]
         (iterate-value 'actions 'fallback 'backup 'steps 'initial))]
    {:value-function value-function :operator operator :sequence sequence}))

(defn- successor-equivalence [value-function sequence steps state]
  (let [current (app sequence steps)
        next (app sequence (succ steps))
        image
        (function/lam
         [['selected-state 'S]]
         (optimality-step
          'actions 'fallback 'backup current 'selected-state))
        successor-equality
        (app (function/const* 'value/signed-iterate-successor [U V])
             'S 'A 'actions 'fallback 'backup steps 'initial)]
    (app
     (function/const* 'equality/substitution [data-u])
     value-function next image successor-equality
     (function/lam
      [['candidate value-function]]
      (veq (app next state) (app 'candidate state)))
     (equivalent-reflexive (app next state)))))

(defn- advance-type [value-function operator discount]
  (function/forall
   [['left value-function] ['right value-function]
    ['epsilon signed]
    ['close
     (function/forall
      [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
   (function/forall
    [['state 'S]]
    (close-at (app operator 'left) (app operator 'right)
              (smul discount 'epsilon) 'state))))

(def bellman-successive-iterate-additive-radius-spec
  (let [{:keys [value-function operator sequence]} (bellman-objects)
        initial-image (app operator 'initial)]
    {:name 'value/signed-optimality-successive-iterate-additive-radius
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['discount signed]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial initial-image 'initial-error 'state))]
       ['advance (advance-type value-function operator 'discount)]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (app sequence 'steps) (app sequence (succ 'steps))
                 (error-radius 'discount 'initial-error 'steps) 'state)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['discount signed]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial initial-image 'initial-error 'state))]
       ['advance (advance-type value-function operator 'discount)]]
      (app
       (function/const*
        'value/signed-abstract-successive-iterate-additive-radius [U])
       'S operator sequence 'discount 'initial-error
       (function/lam
        [['steps nat] ['state 'S]]
        (successor-equivalence value-function sequence 'steps 'state))
       'initial-close 'advance))}))

(defn- general-binders []
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        discount (from-nnrat gamma)
        {:keys [value-function operator]} (bellman-objects)]
    [['ap nat] ['gp nat]
     ['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow value-function 'S 'A signed)]
     ['initial value-function] ['initial-error signed]
     ['initial-error-nonnegative (sle signed-zero 'initial-error)]
     ['initial-bound
      (sle 'initial-error
           (general-harmonic-radius 'ap 'gp nat-zero))]
     ['initial-close
      (function/forall
       [['state 'S]]
       (close-at 'initial (app operator 'initial)
                 'initial-error 'state))]
     ['advance (advance-type value-function operator discount)]]))

(def approximate-optimality-fixed-point-general-rate-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        discount (from-nnrat gamma)
        {:keys [value-function operator sequence]} (bellman-objects)
        radius
        (function/lam
         [['steps nat]] (error-radius discount 'initial-error 'steps))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'value/signed-optimality-approximate-fixed-point-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (general-binders)
      (function/forall
       [['index nat] ['state 'S]]
       (close-at (app sequence (app modulus 'index))
                 (app operator (app sequence (app modulus 'index)))
                 (harmonic-radius 'index) 'state)))
     :value
     (function/lam
      (general-binders)
      (function/lam
       [['index nat] ['state 'S]]
       (app
        (function/const*
         'value/signed-rate-certificate-approximate-fixed-point [U])
        'S operator sequence radius modulus
        (function/lam
         [['steps nat] ['selected-state 'S]]
         (successor-equivalence
          value-function sequence 'steps 'selected-state))
        (app
         (function/const*
          'value/signed-optimality-successive-iterate-additive-radius [U V])
         'S 'A 'actions 'fallback 'backup discount
         'initial 'initial-error 'initial-close 'advance)
        (app
         (function/const*
          'analysis/signed-vi-error-radius-rate-null-general [])
         'ap 'gp 'initial-error
         'initial-error-nonnegative 'initial-bound)
        'index 'state)))}))

(def approximate-optimality-fixed-point-exists-general-rate-spec
  (let [{:keys [value-function operator sequence]} (bellman-objects)
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))
        predicate
        (function/lam
         [['candidate value-function]]
         (function/forall
          [['state 'S]]
          (close-at 'candidate (app operator 'candidate)
                    (harmonic-radius 'index) 'state)))]
    {:name 'value/signed-optimality-approximate-fixed-point-exists-general-rate
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
       value-function predicate
       (app sequence (app modulus 'index))
       (function/lam
        [['state 'S]]
        (app
         (function/const*
          'value/signed-optimality-approximate-fixed-point-general-rate [U V])
         'ap 'gp 'S 'A 'actions 'fallback 'backup
         'initial 'initial-error 'initial-error-nonnegative
         'initial-bound 'initial-close 'advance 'index 'state))))}))

(def definition-specs [])
(def theorem-specs
  [bellman-successive-iterate-additive-radius-spec
   approximate-optimality-fixed-point-general-rate-spec
   approximate-optimality-fixed-point-exists-general-rate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-approximate-optimality])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-approximate-optimality-generic theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-approximate-optimality-generic))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
