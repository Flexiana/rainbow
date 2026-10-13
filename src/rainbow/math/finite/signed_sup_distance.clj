(ns rainbow.math.finite.signed-sup-distance
  "A native finite supremum metric for signed-valued functions.

  `metric/finite-signed-sup-distance` folds quotient-safe signed distance over
  an exact finset enumeration with the established signed maximum.  This is the
  function-space counterpart of `vector/sup-distance`, and supplies the metric
  laws needed by residual certificates for finite signed Bellman operators.

  The carrier enumeration need not be exhaustive for the fold laws themselves;
  clients that turn them into carrier-wide claims must retain an explicit
  coverage premise.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.nnrat-sup-distance :as metric-base]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- membership [element source value]
  (app (function/const* 'list/membership [U]) element source value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U]) element source value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- map-max [element mapping source]
  (app (function/const* 'list/signed-map-max [U])
       element mapping source))
(defn- finite-sup-distance [element source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [U])
       element source left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))

(def finite-signed-sup-distance-spec
  {:name 'metric/finite-signed-sup-distance
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    signed)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    (map-max
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'left 'state) (app 'right 'state)))
     (enumeration 'A 'source)))})

(def finite-signed-sup-distance-upper-bound-spec
  (let [pointwise
        (function/lam
         [['state 'A]]
         (scalar-distance (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-signed-sup-distance-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (sle (scalar-distance (app 'left 'state) (app 'right 'state))
           (finite-sup-distance 'A 'source 'left 'right)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (app (function/const* 'list/signed-map-max-upper-bound [U])
           'A pointwise (enumeration 'A 'source) 'state 'member))}))

(def finite-signed-sup-distance-bounded-spec
  (let [pointwise-distance
        (function/lam
         [['state 'A]]
         (scalar-distance (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-signed-sup-distance-bounded
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['upper signed]
       ['zero-upper (sle signed-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (sle (scalar-distance (app 'left 'state) (app 'right 'state))
              'upper))]]
      (sle (finite-sup-distance 'A 'source 'left 'right) 'upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]
       ['upper signed]
       ['zero-upper (sle signed-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (sle (scalar-distance (app 'left 'state) (app 'right 'state))
              'upper))]]
      (app (function/const* 'list/signed-map-max-bounded [U])
           'A pointwise-distance 'upper 'zero-upper
           (enumeration 'A 'source)
           (function/lam
            [['state 'A]
             ['member
              (membership 'A (enumeration 'A 'source) 'state)]]
            (app 'pointwise 'state 'member))))}))

(def finite-signed-sup-distance-nonnegative-spec
  {:name 'metric/finite-signed-sup-distance-nonnegative
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    (sle signed-zero
         (finite-sup-distance 'A 'source 'left 'right)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    (app
     (function/const* 'list/signed-map-max-nonnegative [U])
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'left 'state) (app 'right 'state)))
     (enumeration 'A 'source)))})

(def finite-signed-sup-distance-symmetric-spec
  {:name 'metric/finite-signed-sup-distance-symmetric
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    (veq (finite-sup-distance 'A 'source 'left 'right)
         (finite-sup-distance 'A 'source 'right 'left)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]]
    (app
     (function/const* 'list/signed-map-max-congruent [U])
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'left 'state) (app 'right 'state)))
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'right 'state) (app 'left 'state)))
     (function/lam
      [['state 'A]]
      (app (function/const* 'signed/distance-symmetric [])
           (app 'left 'state) (app 'right 'state)))
     (enumeration 'A 'source)))})

(def finite-signed-sup-distance-triangle-spec
  (let [left-middle (finite-sup-distance 'A 'source 'left 'middle)
        middle-right (finite-sup-distance 'A 'source 'middle 'right)
        upper (sadd left-middle middle-right)
        left-right-mapping
        (function/lam
         [['state 'A]]
         (scalar-distance (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-signed-sup-distance-triangle
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['middle (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]]
      (sle (finite-sup-distance 'A 'source 'left 'right) upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A signed)]
       ['middle (function/arrow 'A signed)]
       ['right (function/arrow 'A signed)]]
      (let [left-middle-nonnegative
            (app
             (function/const*
              'metric/finite-signed-sup-distance-nonnegative [U])
             'A 'source 'left 'middle)
            middle-right-nonnegative
            (app
             (function/const*
              'metric/finite-signed-sup-distance-nonnegative [U])
             'A 'source 'middle 'right)
            zero-sum (sadd signed-zero signed-zero)
            zero-upper
            (order-respects
             zero-sum signed-zero upper upper
             (app (function/const* 'signed/add-zero-right []) signed-zero)
             (equivalent-reflexive upper)
             (app (function/const* 'signed/add-monotone [])
                  signed-zero left-middle
                  signed-zero middle-right
                  left-middle-nonnegative middle-right-nonnegative))]
        (app
         (function/const* 'list/signed-map-max-bounded [U])
         'A left-right-mapping upper zero-upper
         (enumeration 'A 'source)
         (function/lam
          [['state 'A]
           ['member
            (membership 'A (enumeration 'A 'source) 'state)]]
          (let [left-value (app 'left 'state)
                middle-value (app 'middle 'state)
                right-value (app 'right 'state)
                direct (scalar-distance left-value right-value)
                through
                (sadd (scalar-distance left-value middle-value)
                      (scalar-distance middle-value right-value))
                components
                (app
                 (function/const* 'signed/add-monotone [])
                 (scalar-distance left-value middle-value) left-middle
                 (scalar-distance middle-value right-value) middle-right
                 (app
                  (function/const*
                   'metric/finite-signed-sup-distance-upper-bound [U])
                  'A 'source 'left 'middle 'state 'member)
                 (app
                  (function/const*
                   'metric/finite-signed-sup-distance-upper-bound [U])
                  'A 'source 'middle 'right 'state 'member))]
            (order-transitive
             direct through upper
             (app (function/const* 'signed/distance-triangle [])
                  left-value middle-value right-value)
             components))))))}))

(def definition-specs [finite-signed-sup-distance-spec])
(def theorem-specs
  [finite-signed-sup-distance-upper-bound-spec
   finite-signed-sup-distance-bounded-spec
   finite-signed-sup-distance-nonnegative-spec
   finite-signed-sup-distance-symmetric-spec
   finite-signed-sup-distance-triangle-spec])

(defn extend-environment [env]
  (-> env
      metric-base/extend-environment
      (support/extend-with :finite-signed-sup-distance
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
