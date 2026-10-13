(ns rainbow.math.finite.nnrat-sup-distance
  "A native finite supremum metric for NNRAT-valued functions.

  Bellman values are functions into exact nonnegative rationals, while Rainbow's
  existing finite function metric is Nat-valued and its signed supremum metric
  is list-vector-specific.  This module closes that representation gap without
  inventing quotient subtraction on NNRAT: each value is embedded canonically
  with `signed/from-nnrat`, scalar distance is the existing quotient-safe signed
  distance, and the finite maximum is the existing signed map-max fold over the
  exact finset enumeration.

  The result has the laws needed by a posteriori Bellman certificates: every
  enumerated component is below the supremum, pointwise bounds fold globally,
  and the metric is nonnegative, symmetric, and triangular.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-triangle :as sup-triangle]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [data-level]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [data-level]) element head tail))
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
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- map-max [element mapping source]
  (app (function/const* 'list/signed-map-max [U])
       element mapping source))
(defn- finite-sup-distance [element source left right]
  (app (function/const* 'metric/finite-nnrat-sup-distance [U])
       element source left right))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- max-left [left right]
  (app (function/const* 'signed/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- signed-equivalent-of-equality [left right same]
  (app (function/const* 'signed/equivalent-of-equality [])
       left right same))
(defn- congruent [source target mapping left right same]
  (app (function/const* 'equality/congruent-function
                        [data-level type-level])
       source target mapping left right same))

(def finite-nnrat-sup-distance-spec
  {:name 'metric/finite-nnrat-sup-distance
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    signed)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (map-max
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance
       (from-nnrat (app 'left 'state))
       (from-nnrat (app 'right 'state))))
     (enumeration 'A 'source)))})

(def signed-map-max-upper-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (sle (app 'mapping 'value)
               (map-max 'A 'mapping 'source))))]
    {:name 'list/signed-map-max-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A signed)]
       ['source (list-of 'A)] ['value 'A]
       ['member (membership 'A 'source 'value)]]
      (sle (app 'mapping 'value)
           (map-max 'A 'mapping 'source)))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A signed)]
       ['source (list-of 'A)]]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['value 'A]
         ['impossible (membership 'A (nil-list 'A) 'value)]]
        (app (function/const* 'proposition/explode [])
             (sle (app 'mapping 'value) signed-zero)
             'impossible))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (app motive 'tail)]
         ['value 'A]
         ['member
          (membership 'A (cons-list 'A 'head 'tail) 'value)]]
        (let [head-case (function/equality data-level 'A 'value 'head)
              tail-case (membership 'A 'tail 'value)
              head-value (app 'mapping 'head)
              tail-maximum (map-max 'A 'mapping 'tail)
              target (sle (app 'mapping 'value)
                          (maximum head-value tail-maximum))]
          (app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (let [value-equality
                  (congruent 'A signed 'mapping 'value 'head 'same)
                  value-equivalent-head
                  (signed-equivalent-of-equality
                   (app 'mapping 'value) head-value value-equality)]
              (order-respects
               head-value (app 'mapping 'value)
               (maximum head-value tail-maximum)
               (maximum head-value tail-maximum)
               (equivalent-symmetric
                (app 'mapping 'value) head-value
                value-equivalent-head)
               (equivalent-reflexive
                (maximum head-value tail-maximum))
               (max-left head-value tail-maximum))))
           (function/lam
            [['tail-member tail-case]]
            (order-transitive
             (app 'mapping 'value) tail-maximum
             (maximum head-value tail-maximum)
             (app 'induction-hypothesis 'value 'tail-member)
             (max-right head-value tail-maximum))))))
       'source))}))

(def finite-nnrat-sup-distance-upper-bound-spec
  (let [pointwise
        (function/lam
         [['state 'A]]
         (scalar-distance
          (from-nnrat (app 'left 'state))
          (from-nnrat (app 'right 'state))))]
    {:name 'metric/finite-nnrat-sup-distance-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (sle
       (scalar-distance
        (from-nnrat (app 'left 'state))
        (from-nnrat (app 'right 'state)))
       (finite-sup-distance 'A 'source 'left 'right)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (app (function/const* 'list/signed-map-max-upper-bound [U])
           'A pointwise (enumeration 'A 'source) 'state 'member))}))

(def finite-nnrat-sup-distance-bounded-spec
  (let [pointwise-distance
        (function/lam
         [['state 'A]]
         (scalar-distance
          (from-nnrat (app 'left 'state))
          (from-nnrat (app 'right 'state))))]
    {:name 'metric/finite-nnrat-sup-distance-bounded
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['upper signed]
       ['zero-upper (sle signed-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (sle
          (scalar-distance
           (from-nnrat (app 'left 'state))
           (from-nnrat (app 'right 'state)))
          'upper))]]
      (sle (finite-sup-distance 'A 'source 'left 'right) 'upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['upper signed]
       ['zero-upper (sle signed-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (sle
          (scalar-distance
           (from-nnrat (app 'left 'state))
           (from-nnrat (app 'right 'state)))
          'upper))]]
      (app (function/const* 'list/signed-map-max-bounded [U])
           'A pointwise-distance 'upper 'zero-upper
           (enumeration 'A 'source)
           (function/lam
            [['state 'A]
             ['member
              (membership 'A (enumeration 'A 'source) 'state)]]
            (app 'pointwise 'state 'member))))}))

(def finite-nnrat-sup-distance-nonnegative-spec
  {:name 'metric/finite-nnrat-sup-distance-nonnegative
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (sle signed-zero
         (finite-sup-distance 'A 'source 'left 'right)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (app
     (function/const* 'list/signed-map-max-nonnegative [U])
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance
       (from-nnrat (app 'left 'state))
       (from-nnrat (app 'right 'state))))
     (enumeration 'A 'source)))})

(def finite-nnrat-sup-distance-symmetric-spec
  {:name 'metric/finite-nnrat-sup-distance-symmetric
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (veq (finite-sup-distance 'A 'source 'left 'right)
         (finite-sup-distance 'A 'source 'right 'left)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (app
     (function/const* 'list/signed-map-max-congruent [U])
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance
       (from-nnrat (app 'left 'state))
       (from-nnrat (app 'right 'state))))
     (function/lam
      [['state 'A]]
      (scalar-distance
       (from-nnrat (app 'right 'state))
       (from-nnrat (app 'left 'state))))
     (function/lam
      [['state 'A]]
      (app (function/const* 'signed/distance-symmetric [])
           (from-nnrat (app 'left 'state))
           (from-nnrat (app 'right 'state))))
     (enumeration 'A 'source)))})

(def finite-nnrat-sup-distance-triangle-spec
  (let [left-middle
        (finite-sup-distance 'A 'source 'left 'middle)
        middle-right
        (finite-sup-distance 'A 'source 'middle 'right)
        upper (sadd left-middle middle-right)
        left-right-mapping
        (function/lam
         [['state 'A]]
         (scalar-distance
          (from-nnrat (app 'left 'state))
          (from-nnrat (app 'right 'state))))]
    {:name 'metric/finite-nnrat-sup-distance-triangle
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['middle (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]]
      (sle (finite-sup-distance 'A 'source 'left 'right)
           upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['middle (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]]
      (let [left-middle-nonnegative
            (app
             (function/const*
              'metric/finite-nnrat-sup-distance-nonnegative [U])
             'A 'source 'left 'middle)
            middle-right-nonnegative
            (app
             (function/const*
              'metric/finite-nnrat-sup-distance-nonnegative [U])
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
          (let [left-value (from-nnrat (app 'left 'state))
                middle-value (from-nnrat (app 'middle 'state))
                right-value (from-nnrat (app 'right 'state))
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
                   'metric/finite-nnrat-sup-distance-upper-bound [U])
                  'A 'source 'left 'middle 'state 'member)
                 (app
                  (function/const*
                   'metric/finite-nnrat-sup-distance-upper-bound [U])
                  'A 'source 'middle 'right 'state 'member))]
            (order-transitive
             direct through upper
             (app (function/const* 'signed/distance-triangle [])
                  left-value middle-value right-value)
             components))))))}))

(def definition-specs [finite-nnrat-sup-distance-spec])

(def theorem-specs
  [signed-map-max-upper-bound-spec
   finite-nnrat-sup-distance-upper-bound-spec
   finite-nnrat-sup-distance-bounded-spec
   finite-nnrat-sup-distance-nonnegative-spec
   finite-nnrat-sup-distance-symmetric-spec
   finite-nnrat-sup-distance-triangle-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.vector-sup-triangle])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-nnrat-sup-distance (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.nnrat-sup-distance))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
