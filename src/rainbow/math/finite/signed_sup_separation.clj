(ns rainbow.math.finite.signed-sup-separation
  "Exact separation for finite signed-valued function sup distance.

  Pointwise signed equivalence on every enumerated member is equivalent to zero
  finite sup distance.  The converse is intentionally scoped to the finset's
  members; a client claiming equality over an entire carrier must separately
  provide exhaustiveness.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.signed-sup-distance :as metric]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U])
       element source value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- finite-distance [element source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [U])
       element source left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'signed/equivalent-to-at-most [])
       left right same))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))

(def finite-distance-zero-of-pointwise-equivalent-spec
  {:name 'metric/finite-signed-sup-distance-zero-of-pointwise-equivalent
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['pointwise
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (veq (app 'left 'state) (app 'right 'state)))]]
    (veq (finite-distance 'A 'source 'left 'right) signed-zero))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['pointwise
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (veq (app 'left 'state) (app 'right 'state)))]]
    (let [radius (finite-distance 'A 'source 'left 'right)
          radius-at-most-zero
          (app
           (function/const*
            'metric/finite-signed-sup-distance-bounded [U])
           'A 'source 'left 'right signed-zero
           (order-reflexive signed-zero)
           (function/lam
            [['state 'A]
             ['member (source-membership 'A 'source 'state)]]
            (let [distance
                  (scalar-distance
                   (app 'left 'state) (app 'right 'state))
                  distance-zero
                  (app (function/const* 'signed/distance-zero-of-equivalent [])
                       (app 'left 'state) (app 'right 'state)
                       (app 'pointwise 'state 'member))]
              (equivalent-to-at-most
               distance signed-zero distance-zero))))
          zero-at-most-radius
          (app
           (function/const*
            'metric/finite-signed-sup-distance-nonnegative [U])
           'A 'source 'left 'right)]
      (antisymmetric radius signed-zero
                     radius-at-most-zero zero-at-most-radius)))})

(def pointwise-equivalent-of-finite-distance-zero-spec
  {:name 'metric/pointwise-equivalent-of-finite-signed-sup-distance-zero
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['radius-zero
      (veq (finite-distance 'A 'source 'left 'right) signed-zero)]]
    (function/forall
     [['state 'A]
      ['member (source-membership 'A 'source 'state)]]
     (veq (app 'left 'state) (app 'right 'state))))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['radius-zero
      (veq (finite-distance 'A 'source 'left 'right) signed-zero)]
     ['state 'A]
     ['member (source-membership 'A 'source 'state)]]
    (let [left-at (app 'left 'state)
          right-at (app 'right 'state)
          distance (scalar-distance left-at right-at)
          radius (finite-distance 'A 'source 'left 'right)
          distance-at-most-radius
          (app
           (function/const*
            'metric/finite-signed-sup-distance-upper-bound [U])
           'A 'source 'left 'right 'state 'member)
          distance-at-most-zero
          (order-respects
           distance distance radius signed-zero
           (equivalent-reflexive distance) 'radius-zero
           distance-at-most-radius)
          zero-at-most-distance
          (app (function/const* 'signed/distance-nonnegative [])
               left-at right-at)
          distance-zero
          (antisymmetric distance signed-zero
                         distance-at-most-zero zero-at-most-distance)]
      (app (function/const* 'signed/equivalent-of-distance-zero [])
           left-at right-at distance-zero)))})

(def finite-distance-zero-iff-pointwise-equivalent-spec
  (let [radius-zero
        (veq (finite-distance 'A 'source 'left 'right) signed-zero)
        pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (veq (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-signed-sup-distance-zero-iff-pointwise-equivalent
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]]
      (proposition/equivalence radius-zero pointwise))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]]
      (app
       (function/const* 'proposition/equivalence-intro [])
       radius-zero pointwise
       (function/lam
        [['zero-radius radius-zero]]
        (app
         (function/const*
          'metric/pointwise-equivalent-of-finite-signed-sup-distance-zero
          [U])
         'A 'source 'left 'right 'zero-radius))
       (function/lam
        [['same pointwise]]
        (app
         (function/const*
          'metric/finite-signed-sup-distance-zero-of-pointwise-equivalent
          [U])
         'A 'source 'left 'right 'same))))}))

(def definition-specs [])
(def theorem-specs
  [finite-distance-zero-of-pointwise-equivalent-spec
   pointwise-equivalent-of-finite-distance-zero-spec
   finite-distance-zero-iff-pointwise-equivalent-spec])

(defn extend-environment [env]
  (-> env
      metric/extend-environment
      (support/extend-with :finite-signed-sup-separation theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
