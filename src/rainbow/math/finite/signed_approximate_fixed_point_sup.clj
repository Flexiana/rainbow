(ns rainbow.math.finite.signed-approximate-fixed-point-sup
  "Finite-sup certificates from pointwise signed approximate fixed points.

  A whole-carrier two-sided additive epsilon bound implies a signed-distance
  bound at every enumerated state and therefore a finite sup-residual bound.
  The existential bridge preserves the same witness, turning a pointwise
  approximate fixed-point existence theorem into a scalar certificate suitable
  for an independent verifier.  No carrier-exhaustiveness premise is needed:
  the input already quantifies over every state, while the output deliberately
  measures only the declared finite source.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.math.finite.bellman-signed-approximate-optimality-generic
             :as approximate]
            [rainbow.math.finite.signed-sup-distance :as finite-sup]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U]) element source value))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- finite-sup-distance [element source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [U])
       element source left right))
(defn- close-at [left right epsilon state]
  (proposition/conjunction
   (sle (app left state) (sadd (app right state) epsilon))
   (sle (app right state) (sadd (app left state) epsilon))))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def pointwise-additive-closeness-bounds-finite-sup-spec
  (let [value-function (function/arrow 'S signed)]
    {:name 'metric/finite-signed-sup-distance-bounded-by-pointwise-additive-closeness
     :universes ['u]
     :type
     (function/forall
      [['S type-u] ['source (exact-finset-of 'S)]
       ['left value-function] ['right value-function]
       ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-close
        (function/forall
         [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
      (sle (finite-sup-distance 'S 'source 'left 'right) 'epsilon))
     :value
     (function/lam
      [['S type-u] ['source (exact-finset-of 'S)]
       ['left value-function] ['right value-function]
       ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-close
        (function/forall
         [['state 'S]] (close-at 'left 'right 'epsilon 'state))]]
      (app
       (function/const* 'metric/finite-signed-sup-distance-bounded [U])
       'S 'source 'left 'right 'epsilon 'epsilon-nonnegative
       (function/lam
        [['state 'S]
         ['ignored-member (source-membership 'S 'source 'state)]]
        (let [left-value (app 'left 'state)
              right-value (app 'right 'state)
              left-close
              (sle left-value (sadd right-value 'epsilon))
              right-close
              (sle right-value (sadd left-value 'epsilon))
              both (app 'pointwise-close 'state)]
          (app
           (function/const*
            'signed/distance-at-most-of-additive-closeness [])
           left-value right-value 'epsilon
           (left-conjunct left-close right-close both)
           (right-conjunct left-close right-close both))))))}))

(def pointwise-approximate-fixed-point-sup-certificate-spec
  (let [value-function (function/arrow 'S signed)
        image (app 'operator 'candidate)]
    {:name 'value/signed-pointwise-approximate-fixed-point-sup-certificate
     :universes ['u]
     :type
     (function/forall
      [['S type-u] ['source (exact-finset-of 'S)]
       ['operator (function/arrow value-function value-function)]
       ['candidate value-function] ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-close
        (function/forall
         [['state 'S]]
         (close-at 'candidate image 'epsilon 'state))]]
      (sle (finite-sup-distance 'S 'source 'candidate image) 'epsilon))
     :value
     (function/lam
      [['S type-u] ['source (exact-finset-of 'S)]
       ['operator (function/arrow value-function value-function)]
       ['candidate value-function] ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-close
        (function/forall
         [['state 'S]]
         (close-at 'candidate image 'epsilon 'state))]]
      (app
       (function/const*
        'metric/finite-signed-sup-distance-bounded-by-pointwise-additive-closeness
        [U])
       'S 'source 'candidate image 'epsilon
       'epsilon-nonnegative 'pointwise-close))}))

(def pointwise-existence-gives-sup-existence-spec
  (let [value-function (function/arrow 'S signed)
        pointwise-predicate
        (function/lam
         [['candidate value-function]]
         (function/forall
          [['state 'S]]
          (close-at 'candidate (app 'operator 'candidate)
                    'epsilon 'state)))
        sup-predicate
        (function/lam
         [['candidate value-function]]
         (sle
          (finite-sup-distance
           'S 'source 'candidate (app 'operator 'candidate))
          'epsilon))]
    {:name 'value/signed-pointwise-approximate-fixed-point-existence-gives-sup-existence
     :universes ['u]
     :type
     (function/forall
      [['S type-u] ['source (exact-finset-of 'S)]
       ['operator (function/arrow value-function value-function)]
       ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-exists
        (proposition/existence data-u value-function pointwise-predicate)]]
      (proposition/existence data-u value-function sup-predicate))
     :value
     (function/lam
      [['S type-u] ['source (exact-finset-of 'S)]
       ['operator (function/arrow value-function value-function)]
       ['epsilon signed]
       ['epsilon-nonnegative
        (sle (function/const* 'signed/zero []) 'epsilon)]
       ['pointwise-exists
        (proposition/existence data-u value-function pointwise-predicate)]]
      (app
       (function/const* 'proposition/use-witness [data-u])
       value-function pointwise-predicate
       (proposition/existence data-u value-function sup-predicate)
       'pointwise-exists
       (function/lam
        [['candidate value-function]
         ['pointwise-close (app pointwise-predicate 'candidate)]]
        (app
         (function/const* 'proposition/witness [data-u])
         value-function sup-predicate 'candidate
         (app
          (function/const*
           'value/signed-pointwise-approximate-fixed-point-sup-certificate [U])
          'S 'source 'operator 'candidate 'epsilon
          'epsilon-nonnegative 'pointwise-close)))))}))

(def definition-specs [])
(def theorem-specs
  [pointwise-additive-closeness-bounds-finite-sup-spec
   pointwise-approximate-fixed-point-sup-certificate-spec
   pointwise-existence-gives-sup-existence-spec])

(defn extend-environment [env]
  (-> env
      approximate/extend-environment
      finite-sup/extend-environment
      additive-distance/extend-environment
      (support/extend-with
       :finite-signed-approximate-fixed-point-sup theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
