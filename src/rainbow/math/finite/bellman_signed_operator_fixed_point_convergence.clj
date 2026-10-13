(ns rainbow.math.finite.bellman-signed-operator-fixed-point-convergence
  "Fixed-point convergence of the low-arity signed operator iterator.

  Any pointwise two-sided additively contractive operator transports closeness
  to an assumed fixed point. Structural induction gives the exact recursive
  error radius for every finite iterate; the existing general harmonic theorem
  then packages a rate-null convergence certificate for every canonical
  positive rational discount (a+1)/(a+g+2). No fixed point is constructed.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.bellman-signed-transition-operator
             :as operator-interface]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
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
(defn- iterate-value [operator steps initial]
  (app (function/const* 'value/signed-operator-iterate [U])
       'S operator steps initial))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
(defn- general-harmonic-radius [ap gp steps]
  (from-nnrat
   (app (function/const* 'nnrat/general-harmonic []) ap gp steps)))
(defn- close-at [left right epsilon state]
  (proposition/conjunction
   (sle (app left state) (sadd (app right state) epsilon))
   (sle (app right state) (sadd (app left state) epsilon))))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- add-respects
  [left left-prime right right-prime left-same right-same]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- order-respects
  [left left-prime right right-prime left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))

(def signed-operator-iterate-zero-spec
  (let [value-function (function/arrow 'S signed)
        initial-iterate (iterate-value 'operator nat-zero 'initial)]
    {:name 'value/signed-operator-iterate-zero
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['initial value-function]]
      (function/equality data-u value-function initial-iterate 'initial))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['initial value-function]]
      (app (function/const* 'equality/reflexive [data-u])
           value-function 'initial))}))

(def signed-contractive-operator-fixed-point-advance-spec
  (let [value-function (function/arrow 'S signed)
        operator-at (fn [value] (app 'operator value))
        scaled (smul 'discount 'epsilon)]
    {:name 'value/signed-contractive-operator-fixed-point-additive-advance
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['discount signed]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (app (operator-at 'fixed-value) 'state)
              (app 'fixed-value 'state)))]
       ['candidate value-function] ['epsilon signed]
       ['candidate-close
        (function/forall
         [['state 'S]]
         (close-at 'candidate 'fixed-value 'epsilon 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['radius signed]
          ['close
           (function/forall
            [['state 'S]] (close-at 'left 'right 'radius 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (operator-at 'left) (operator-at 'right)
                    (smul 'discount 'radius) 'state)))]
       ['state 'S]]
      (close-at (operator-at 'candidate) 'fixed-value scaled 'state))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['discount signed]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (app (operator-at 'fixed-value) 'state)
              (app 'fixed-value 'state)))]
       ['candidate value-function] ['epsilon signed]
       ['candidate-close
        (function/forall
         [['state 'S]]
         (close-at 'candidate 'fixed-value 'epsilon 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['radius signed]
          ['close
           (function/forall
            [['state 'S]] (close-at 'left 'right 'radius 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (operator-at 'left) (operator-at 'right)
                    (smul 'discount 'radius) 'state)))]
       ['state 'S]]
      (let [candidate-image (app (operator-at 'candidate) 'state)
            fixed-image (app (operator-at 'fixed-value) 'state)
            fixed-at (app 'fixed-value 'state)
            fixed-same (app 'fixed-point 'state)
            raw (app 'advance 'candidate 'fixed-value 'epsilon
                     'candidate-close 'state)
            raw-left
            (sle candidate-image (sadd fixed-image scaled))
            raw-right
            (sle fixed-image (sadd candidate-image scaled))
            right-same
            (add-respects
             fixed-image fixed-at scaled scaled fixed-same
             (equivalent-reflexive scaled))]
        (conjoin
         (sle candidate-image (sadd fixed-at scaled))
         (sle fixed-at (sadd candidate-image scaled))
         (order-respects
          candidate-image candidate-image
          (sadd fixed-image scaled) (sadd fixed-at scaled)
          (equivalent-reflexive candidate-image) right-same
          (left-conjunct raw-left raw-right raw))
         (order-respects
          fixed-image fixed-at
          (sadd candidate-image scaled) (sadd candidate-image scaled)
          fixed-same (equivalent-reflexive (sadd candidate-image scaled))
          (right-conjunct raw-left raw-right raw)))))}))

(def signed-contractive-operator-iterate-fixed-point-radius-spec
  (let [value-function (function/arrow 'S signed)
        iterated (fn [steps] (iterate-value 'operator steps 'initial))
        radius (fn [steps] (error-radius 'discount 'initial-error steps))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (close-at (iterated 'steps) 'fixed-value
                    (radius 'steps) 'state)))
        binders
        [['S type-u]
         ['operator (function/arrow value-function value-function)]
         ['discount signed]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (veq (app (app 'operator 'fixed-value) 'state)
                (app 'fixed-value 'state)))]
         ['initial value-function] ['initial-error signed]
         ['initial-close
          (function/forall
           [['state 'S]]
           (close-at 'initial 'fixed-value 'initial-error 'state))]
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
                      (smul 'discount 'epsilon) 'state)))]]]
    {:name
     'value/signed-contractive-operator-iterate-fixed-point-additive-radius
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (iterated 'steps) 'fixed-value
                 (radius 'steps) 'state)))
     :value
     (function/lam
      binders
      (function/lam
       [['steps nat]]
       (app
        (function/const* 'data/Nat.rec [zero-level])
        motive 'initial-close
        (function/lam
         [['previous nat]
          ['previous-close (app motive 'previous)]]
         (function/lam
          [['state 'S]]
          (app
           (function/const*
            'value/signed-contractive-operator-fixed-point-additive-advance
            [U])
           'S 'operator 'discount 'fixed-value 'fixed-point
           (iterated 'previous) (radius 'previous)
           'previous-close 'advance 'state)))
        'steps)))}))

(def signed-contractive-operator-fixed-point-converges-general-rate-spec
  (let [value-function (function/arrow 'S signed)
        gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        discount (from-nnrat gamma)
        sequence
        (function/lam
         [['steps nat]] (iterate-value 'operator 'steps 'initial))
        radius
        (function/lam
         [['steps nat]] (error-radius discount 'initial-error 'steps))
        modulus
        (function/lam [['index nat]] (nmul (succ 'ap) 'index))
        bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (close-at (app sequence 'steps) 'fixed-value
                   (app radius 'steps) 'state))
        binders
        [['ap nat] ['gp nat]
         ['S type-u]
         ['operator (function/arrow value-function value-function)]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (veq (app (app 'operator 'fixed-value) 'state)
                (app 'fixed-value 'state)))]
         ['initial value-function] ['initial-error signed]
         ['initial-error-nonnegative (sle signed-zero 'initial-error)]
         ['initial-bound
          (sle 'initial-error
               (general-harmonic-radius 'ap 'gp nat-zero))]
         ['initial-close
          (function/forall
           [['state 'S]]
           (close-at 'initial 'fixed-value 'initial-error 'state))]
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
     'value/signed-contractive-operator-iterate-fixed-point-converges-general-rate
     :universes ['u]
     :type
     (function/forall
      binders
      (proposition/conjunction
       (signed-rate-null radius modulus) bounds))
     :value
     (function/lam
      binders
      (conjoin
       (signed-rate-null radius modulus) bounds
       (app
        (function/const*
         'analysis/signed-vi-error-radius-rate-null-general [])
        'ap 'gp 'initial-error
        'initial-error-nonnegative 'initial-bound)
       (app
        (function/const*
         'value/signed-contractive-operator-iterate-fixed-point-additive-radius
         [U])
        'S 'operator discount 'fixed-value 'fixed-point
        'initial 'initial-error 'initial-close 'advance)))}))

(def definition-specs [])
(def theorem-specs
  [signed-operator-iterate-zero-spec
   signed-contractive-operator-fixed-point-advance-spec
   signed-contractive-operator-iterate-fixed-point-radius-spec
   signed-contractive-operator-fixed-point-converges-general-rate-spec])

(defn extend-environment [env]
  (-> env
      operator-interface/extend-environment
      (support/extend-with
       :finite-bellman-signed-operator-fixed-point-convergence
       theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
