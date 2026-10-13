(ns rainbow.math.rational.signed.vector-sup-distance
  "Finite maxima and sup distance for signed-rational list vectors.

  The older V1.54 metric is Nat-valued over functions on an explicit finite
  carrier.  Affine Rainbow states are lists of signed rationals, so this module
  supplies the representation bridge they actually need: a universe-polymorphic
  signed map-max fold with zero base, and the maximum component distance of two
  signed lists.  The fold has structural, nonnegativity, boundedness, and
  congruence laws.  Vector sup distance has a component-bound predicate,
  structural equations, nonnegativity, a global pointwise upper bound,
  symmetry, and zero on the diagonal.  Native, kernel-checked, and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance :as distance]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [data-level]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [data-level]) element head tail))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- membership [element source value]
  (app (function/const* 'list/membership [U]) element source value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- absolute [value]
  (app (function/const* 'signed/absolute []) value))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- map-max [element mapping source]
  (app (function/const* 'list/signed-map-max [U])
       element mapping source))
(defn- vector-sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- within [upper left right]
  (app (function/const* 'vector/within []) upper left right))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- left-proof [left right evidence]
  (app (function/const* 'proposition/left []) left right evidence))
(defn- right-proof [left right evidence]
  (app (function/const* 'proposition/right []) left right evidence))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- max-below [left right upper left-upper right-upper]
  (app (function/const* 'signed/at-most-max [])
       left right upper left-upper right-upper))
(defn- max-respects [left right left-prime right-prime
                     same-left same-right]
  (app (function/const* 'signed/max-respects-equivalence [])
       left right left-prime right-prime same-left same-right))
(defn- signed-equality [left right]
  (function/equality type-level signed left right))
(defn- equality-reflexive [value]
  (app (function/const* 'equality/reflexive [type-level])
       signed value))
(defn- equivalent-of-equality [left right same]
  (app
   (function/const* 'equality/substitution [type-level])
   signed left right same
   (function/lam [['candidate signed]] (veq left 'candidate))
   (equivalent-reflexive left)))
(defn- absolute-mapping []
  (function/lam [['value signed]] (absolute 'value)))

(def signed-map-max-spec
  {:name 'list/signed-map-max :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A signed)]]
    (function/arrow (list-of 'A) signed))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A signed)]
     ['source (list-of 'A)]]
    (app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] signed)
     signed-zero
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-maximum signed]]
      (maximum (app 'mapping 'head) 'tail-maximum))
     'source))})

(def vector-sup-distance-spec
  {:name 'vector/sup-distance :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type signed)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam
       [['ignored vector-type]]
       (function/arrow vector-type signed))
      (function/lam [['ignored vector-type]] signed-zero)
      (function/lam
       [['left-head signed] ['left-tail vector-type]
        ['tail-distance (function/arrow vector-type signed)]]
       (function/lam
        [['remaining vector-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] signed)
         signed-zero
         (function/lam
          [['right-head signed] ['right-tail vector-type]
           ['ignored signed]]
          (maximum (scalar-distance 'left-head 'right-head)
                   (app 'tail-distance 'right-tail)))
         'remaining)))
      'left)
     'right))})

(def within-spec
  {:name 'vector/within :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed vector-type vector-type 'Prop)
   :value
   (function/lam
    [['upper signed] ['left vector-type] ['right vector-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam
       [['ignored vector-type]]
       (function/arrow vector-type 'Prop))
      (function/lam
       [['ignored vector-type]]
       (function/const* 'proposition/truth []))
      (function/lam
       [['left-head signed] ['left-tail vector-type]
        ['tail-within (function/arrow vector-type 'Prop)]]
       (function/lam
        [['remaining vector-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] 'Prop)
         (function/const* 'proposition/truth [])
         (function/lam
          [['right-head signed] ['right-tail vector-type]
           ['ignored 'Prop]]
          (both (sle (scalar-distance 'left-head 'right-head) 'upper)
                (app 'tail-within 'right-tail)))
         'remaining)))
      'left)
     'right))})

(def signed-map-max-empty-spec
  {:name 'list/signed-map-max-empty :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A signed)]]
    (veq (map-max 'A 'mapping (nil-list 'A)) signed-zero))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A signed)]]
    (equivalent-reflexive signed-zero))})

(def signed-equivalent-of-equality-spec
  {:name 'signed/equivalent-of-equality :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (signed-equality 'left 'right)]]
    (veq 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (signed-equality 'left 'right)]]
    (equivalent-of-equality 'left 'right 'same))})

(def signed-map-max-cons-spec
  {:name 'list/signed-map-max-cons :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A signed)]
     ['head 'A] ['tail (list-of 'A)]]
    (veq (map-max 'A 'mapping (cons-list 'A 'head 'tail))
         (maximum (app 'mapping 'head)
                  (map-max 'A 'mapping 'tail))))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A signed)]
     ['head 'A] ['tail (list-of 'A)]]
    (equivalent-reflexive
     (maximum (app 'mapping 'head)
              (map-max 'A 'mapping 'tail))))})

(def signed-map-max-nonnegative-spec
  {:name 'list/signed-map-max-nonnegative :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A signed)]
     ['source (list-of 'A)]]
    (sle signed-zero (map-max 'A 'mapping 'source)))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A signed)]
     ['source (list-of 'A)]]
    (let [motive
          (function/lam
           [['current (list-of 'A)]]
           (sle signed-zero (map-max 'A 'mapping 'current)))]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (order-reflexive signed-zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['tail-nonnegative
          (sle signed-zero (map-max 'A 'mapping 'tail))]]
        (order-transitive
         signed-zero
         (map-max 'A 'mapping 'tail)
         (maximum (app 'mapping 'head)
                  (map-max 'A 'mapping 'tail))
         'tail-nonnegative
         (max-right (app 'mapping 'head)
                    (map-max 'A 'mapping 'tail))))
       'source)))})

(def signed-map-max-bounded-spec
  (let [bounded
        (fn [mapping upper source]
          (function/forall
           [['value 'A]
            ['member (membership 'A source 'value)]]
           (sle (app mapping 'value) upper)))]
    {:name 'list/signed-map-max-bounded :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A signed)]
       ['upper signed] ['zero-upper (sle signed-zero 'upper)]
       ['source (list-of 'A)]
       ['pointwise (bounded 'mapping 'upper 'source)]]
      (sle (map-max 'A 'mapping 'source) 'upper))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A signed)]
       ['upper signed] ['zero-upper (sle signed-zero 'upper)]
       ['source (list-of 'A)]]
      (let [motive
            (function/lam
             [['current (list-of 'A)]]
             (function/arrow
              (bounded 'mapping 'upper 'current)
              (sle (map-max 'A 'mapping 'current) 'upper)))]
        (app
         (function/const* 'data/List.rec [data-level zero-level])
         'A motive
         (function/lam
          [['ignored (bounded 'mapping 'upper (nil-list 'A))]]
          'zero-upper)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['tail-bounded
            (function/arrow
             (bounded 'mapping 'upper 'tail)
             (sle (map-max 'A 'mapping 'tail) 'upper))]
           ['pointwise
            (bounded 'mapping 'upper
                     (cons-list 'A 'head 'tail))]]
          (let [head-equality
                (function/equality data-level 'A 'head 'head)
                head-member
                (app
                 (function/const* 'proposition/left-disjunct [])
                 head-equality (membership 'A 'tail 'head)
                 (app (function/const* 'equality/reflexive [data-level])
                      'A 'head))
                tail-pointwise
                (function/lam
                 [['value 'A]
                  ['tail-member (membership 'A 'tail 'value)]]
                 (app
                  'pointwise 'value
                  (app
                   (function/const* 'proposition/right-disjunct [])
                   (function/equality data-level 'A 'value 'head)
                   (membership 'A 'tail 'value)
                   'tail-member)))]
            (max-below
             (app 'mapping 'head)
             (map-max 'A 'mapping 'tail)
             'upper
             (app 'pointwise 'head head-member)
             (app 'tail-bounded tail-pointwise))))
         'source)))}))

(def signed-map-max-congruent-spec
  {:name 'list/signed-map-max-congruent :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['pointwise
      (function/forall
       [['value 'A]]
       (veq (app 'left 'value) (app 'right 'value)))]
     ['source (list-of 'A)]]
    (veq (map-max 'A 'left 'source)
         (map-max 'A 'right 'source)))
   :value
   (function/lam
    [['A type-u]
     ['left (function/arrow 'A signed)]
     ['right (function/arrow 'A signed)]
     ['pointwise
      (function/forall
       [['value 'A]]
       (veq (app 'left 'value) (app 'right 'value)))]
     ['source (list-of 'A)]]
    (let [motive
          (function/lam
           [['current (list-of 'A)]]
           (veq (map-max 'A 'left 'current)
                (map-max 'A 'right 'current)))]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (equivalent-reflexive signed-zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['tail-same
          (veq (map-max 'A 'left 'tail)
               (map-max 'A 'right 'tail))]]
        (max-respects
         (app 'left 'head) (map-max 'A 'left 'tail)
         (app 'right 'head) (map-max 'A 'right 'tail)
         (app 'pointwise 'head) 'tail-same))
       'source)))})

(def vector-sup-distance-empty-left-spec
  {:name 'vector/sup-distance-empty-left :universes []
   :type
   (function/forall
    [['right vector-type]]
    (veq (vector-sup-distance (nil-vector) 'right) signed-zero))
   :value
   (function/lam
    [['right vector-type]]
    (equivalent-reflexive signed-zero))})

(def vector-sup-distance-empty-right-spec
  {:name 'vector/sup-distance-empty-right :universes []
   :type
   (function/forall
    [['left vector-type]]
    (veq (vector-sup-distance 'left (nil-vector)) signed-zero))
   :value
   (function/lam
    [['left vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (veq (vector-sup-distance 'current (nil-vector)) signed-zero))]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       signed motive
       (equivalent-reflexive signed-zero)
       (function/lam
        [['head signed] ['tail vector-type]
         ['ignored (app motive 'tail)]]
        (equivalent-reflexive signed-zero))
       'left)))})

(def vector-sup-distance-cons-spec
  {:name 'vector/sup-distance-cons :universes []
   :type
   (function/forall
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]]
    (signed-equality
     (vector-sup-distance
      (cons-vector 'left-head 'left-tail)
      (cons-vector 'right-head 'right-tail))
     (maximum
      (scalar-distance 'left-head 'right-head)
      (vector-sup-distance 'left-tail 'right-tail))))
   :value
   (function/lam
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]]
    (equality-reflexive
     (maximum
      (scalar-distance 'left-head 'right-head)
      (vector-sup-distance 'left-tail 'right-tail))))})

(def vector-sup-distance-nonnegative-spec
  {:name 'vector/sup-distance-nonnegative :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (sle signed-zero (vector-sup-distance 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (sle signed-zero
                 (vector-sup-distance 'current-left 'current-right))))
          outer-base
          (function/lam
           [['current-right vector-type]]
           (order-reflexive signed-zero))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-nonnegative (app outer-motive 'left-tail)]]
           (function/lam
            [['current-right vector-type]]
            (let [current-left (cons-vector 'left-head 'left-tail)
                  right-motive
                  (function/lam
                   [['remaining vector-type]]
                   (sle signed-zero
                        (vector-sup-distance current-left 'remaining)))]
              (app
               (function/const* 'data/List.rec [type-level zero-level])
               signed right-motive
               (order-reflexive signed-zero)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (order-transitive
                 signed-zero
                 (vector-sup-distance 'left-tail 'right-tail)
                 (maximum
                  (scalar-distance 'left-head 'right-head)
                  (vector-sup-distance 'left-tail 'right-tail))
                 (app 'tail-nonnegative 'right-tail)
                 (max-right
                  (scalar-distance 'left-head 'right-head)
                  (vector-sup-distance 'left-tail 'right-tail))))
               'current-right))))]
      (app
       (app
        (function/const* 'data/List.rec [type-level zero-level])
        signed outer-motive outer-base outer-step 'left)
       'right)))})

(def vector-sup-distance-cons-bounded-spec
  {:name 'vector/sup-distance-cons-bounded :universes []
   :type
   (function/forall
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]
     ['upper signed]
     ['head-bound
      (sle (scalar-distance 'left-head 'right-head) 'upper)]
     ['tail-bound
      (sle (vector-sup-distance 'left-tail 'right-tail) 'upper)]]
    (sle
     (vector-sup-distance
      (cons-vector 'left-head 'left-tail)
      (cons-vector 'right-head 'right-tail))
     'upper))
   :value
   (function/lam
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]
     ['upper signed]
     ['head-bound
      (sle (scalar-distance 'left-head 'right-head) 'upper)]
     ['tail-bound
      (sle (vector-sup-distance 'left-tail 'right-tail) 'upper)]]
    (let [source
          (vector-sup-distance
           (cons-vector 'left-head 'left-tail)
           (cons-vector 'right-head 'right-tail))
          source-maximum
          (maximum
           (scalar-distance 'left-head 'right-head)
           (vector-sup-distance 'left-tail 'right-tail))
          source-equation
          (app (function/const* 'vector/sup-distance-cons [])
               'left-head 'left-tail 'right-head 'right-tail)
          source-same
          (app (function/const* 'signed/equivalent-of-equality [])
               source source-maximum source-equation)
          maximum-bound
          (max-below
           (scalar-distance 'left-head 'right-head)
           (vector-sup-distance 'left-tail 'right-tail)
           'upper 'head-bound 'tail-bound)]
      (order-respects
       source-maximum source 'upper 'upper
       (equivalent-symmetric source source-maximum source-same)
       (equivalent-reflexive 'upper)
       maximum-bound)))})

(def vector-sup-distance-bounded-spec
  {:name 'vector/sup-distance-bounded :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['upper signed] ['zero-upper (sle signed-zero 'upper)]
     ['pointwise (within 'upper 'left 'right)]]
    (sle (vector-sup-distance 'left 'right) 'upper))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['upper signed] ['zero-upper (sle signed-zero 'upper)]
     ['pointwise (within 'upper 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-upper signed]
             ['current-zero-upper (sle signed-zero 'current-upper)]
             ['current-pointwise
              (within 'current-upper 'current-left 'current-right)]]
            (sle (vector-sup-distance 'current-left 'current-right)
                 'current-upper)))
          outer-base
          (function/lam
           [['current-right vector-type]
            ['current-upper signed]
            ['current-zero-upper (sle signed-zero 'current-upper)]
            ['ignored (within 'current-upper (nil-vector) 'current-right)]]
           'current-zero-upper)
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-bounded (app outer-motive 'left-tail)]]
           (function/lam
            [['current-right vector-type]]
            (let [current-left (cons-vector 'left-head 'left-tail)
                  right-motive
                  (function/lam
                   [['remaining vector-type]]
                   (function/forall
                    [['current-upper signed]
                     ['current-zero-upper
                      (sle signed-zero 'current-upper)]
                     ['current-pointwise
                      (within 'current-upper current-left 'remaining)]]
                    (sle (vector-sup-distance current-left 'remaining)
                         'current-upper)))]
              (app
               (function/const* 'data/List.rec [type-level zero-level])
               signed right-motive
               (function/lam
                [['current-upper signed]
                 ['current-zero-upper
                  (sle signed-zero 'current-upper)]
                 ['ignored
                  (within 'current-upper current-left (nil-vector))]]
                'current-zero-upper)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]
                 ['current-upper signed]
                 ['current-zero-upper
                  (sle signed-zero 'current-upper)]
                 ['current-pointwise
                  (within
                   'current-upper current-left
                   (cons-vector 'right-head 'right-tail))]]
                (let [head-bound
                      (sle (scalar-distance 'left-head 'right-head)
                           'current-upper)
                      tail-within
                      (within 'current-upper 'left-tail 'right-tail)]
                  (app
                   (function/const*
                    'vector/sup-distance-cons-bounded [])
                   'left-head 'left-tail 'right-head 'right-tail
                   'current-upper
                   (left-proof head-bound tail-within
                               'current-pointwise)
                   (app
                    'tail-bounded 'right-tail 'current-upper
                    'current-zero-upper
                    (right-proof head-bound tail-within
                                 'current-pointwise)))))
               'current-right))))]
      (app
       (app
        (function/const* 'data/List.rec [type-level zero-level])
        signed outer-motive outer-base outer-step 'left)
       'right 'upper 'zero-upper 'pointwise)))})

(def vector-sup-distance-cons-symmetric-spec
  {:name 'vector/sup-distance-cons-symmetric :universes []
   :type
   (function/forall
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]
     ['tail-same
      (veq (vector-sup-distance 'left-tail 'right-tail)
           (vector-sup-distance 'right-tail 'left-tail))]]
    (veq
     (vector-sup-distance
      (cons-vector 'left-head 'left-tail)
      (cons-vector 'right-head 'right-tail))
     (vector-sup-distance
      (cons-vector 'right-head 'right-tail)
      (cons-vector 'left-head 'left-tail))))
   :value
   (function/lam
    [['left-head signed] ['left-tail vector-type]
     ['right-head signed] ['right-tail vector-type]
     ['tail-same
      (veq (vector-sup-distance 'left-tail 'right-tail)
           (vector-sup-distance 'right-tail 'left-tail))]]
    (let [left-vector (cons-vector 'left-head 'left-tail)
          right-vector (cons-vector 'right-head 'right-tail)
          source (vector-sup-distance left-vector right-vector)
          source-maximum
          (maximum
           (scalar-distance 'left-head 'right-head)
           (vector-sup-distance 'left-tail 'right-tail))
          target (vector-sup-distance right-vector left-vector)
          target-maximum
          (maximum
           (scalar-distance 'right-head 'left-head)
           (vector-sup-distance 'right-tail 'left-tail))
          source-equation
          (app
           (function/const* 'vector/sup-distance-cons [])
           'left-head 'left-tail 'right-head 'right-tail)
          target-equation
          (app
           (function/const* 'vector/sup-distance-cons [])
           'right-head 'right-tail 'left-head 'left-tail)
          source-same
          (app (function/const* 'signed/equivalent-of-equality [])
               source source-maximum source-equation)
          target-same
          (app (function/const* 'signed/equivalent-of-equality [])
               target target-maximum target-equation)
          maxima-same
          (max-respects
           (scalar-distance 'left-head 'right-head)
           (vector-sup-distance 'left-tail 'right-tail)
           (scalar-distance 'right-head 'left-head)
           (vector-sup-distance 'right-tail 'left-tail)
           (app (function/const* 'signed/distance-symmetric [])
                'left-head 'right-head)
           'tail-same)]
      (equivalent-transitive
       source source-maximum target
       source-same
       (equivalent-transitive
        source-maximum target-maximum target
        maxima-same
        (equivalent-symmetric target target-maximum target-same)))))})

(def vector-sup-distance-empty-symmetric-spec
  {:name 'vector/sup-distance-empty-symmetric :universes []
   :type
   (function/forall
    [['values vector-type]]
    (veq (vector-sup-distance (nil-vector) 'values)
         (vector-sup-distance 'values (nil-vector))))
   :value
   (function/lam
    [['values vector-type]]
    (let [left-distance
          (vector-sup-distance (nil-vector) 'values)
          right-distance
          (vector-sup-distance 'values (nil-vector))]
      (equivalent-transitive
       left-distance signed-zero right-distance
       (app (function/const* 'vector/sup-distance-empty-left [])
            'values)
       (equivalent-symmetric
        right-distance signed-zero
        (app (function/const* 'vector/sup-distance-empty-right [])
             'values)))))})

(def vector-sup-distance-cons-empty-symmetric-spec
  {:name 'vector/sup-distance-cons-empty-symmetric :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]]
    (veq
     (vector-sup-distance (cons-vector 'head 'tail) (nil-vector))
     (vector-sup-distance (nil-vector) (cons-vector 'head 'tail))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]]
    (let [values (cons-vector 'head 'tail)]
      (equivalent-symmetric
       (vector-sup-distance (nil-vector) values)
       (vector-sup-distance values (nil-vector))
       (app
        (function/const* 'vector/sup-distance-empty-symmetric [])
        values))))})

(def vector-sup-distance-cons-symmetric-all-spec
  {:name 'vector/sup-distance-cons-symmetric-all :universes []
   :type
   (function/forall
    [['left-head signed] ['left-tail vector-type]
     ['tail-symmetry
      (function/forall
       [['right-tail vector-type]]
       (veq (vector-sup-distance 'left-tail 'right-tail)
            (vector-sup-distance 'right-tail 'left-tail)))]
     ['right vector-type]]
    (veq
     (vector-sup-distance
      (cons-vector 'left-head 'left-tail) 'right)
     (vector-sup-distance
      'right (cons-vector 'left-head 'left-tail))))
   :value
   (function/lam
    [['left-head signed] ['left-tail vector-type]
     ['tail-symmetry
      (function/forall
       [['right-tail vector-type]]
       (veq (vector-sup-distance 'left-tail 'right-tail)
            (vector-sup-distance 'right-tail 'left-tail)))]
     ['right vector-type]]
    (let [current-left (cons-vector 'left-head 'left-tail)
          motive
          (function/lam
           [['current-right vector-type]]
           (veq (vector-sup-distance current-left 'current-right)
                (vector-sup-distance 'current-right current-left)))]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       signed motive
       (app
        (function/const*
         'vector/sup-distance-cons-empty-symmetric [])
        'left-head 'left-tail)
       (function/lam
        [['right-head signed] ['right-tail vector-type]
         ['ignored (app motive 'right-tail)]]
        (app
         (function/const* 'vector/sup-distance-cons-symmetric [])
         'left-head 'left-tail 'right-head 'right-tail
         (app 'tail-symmetry 'right-tail)))
       'right)))})

(def vector-sup-distance-symmetric-spec
  {:name 'vector/sup-distance-symmetric :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (veq (vector-sup-distance 'left 'right)
         (vector-sup-distance 'right 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (veq (vector-sup-distance 'current-left 'current-right)
                 (vector-sup-distance 'current-right 'current-left))))]
      (app
       (app
        (function/const* 'data/List.rec [type-level zero-level])
        signed motive
        (function/lam
         [['current-right vector-type]]
         (app
          (function/const* 'vector/sup-distance-empty-symmetric [])
          'current-right))
        (function/lam
         [['left-head signed] ['left-tail vector-type]
          ['tail-symmetry (app motive 'left-tail)]]
         (function/lam
          [['current-right vector-type]]
          (app
           (function/const*
            'vector/sup-distance-cons-symmetric-all [])
           'left-head 'left-tail 'tail-symmetry 'current-right)))
        'left)
       'right)))})

(def vector-sup-distance-self-zero-spec
  {:name 'vector/sup-distance-self-zero :universes []
   :type
   (function/forall
    [['values vector-type]]
    (veq (vector-sup-distance 'values 'values) signed-zero))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (veq (vector-sup-distance 'current 'current) signed-zero))]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       signed motive
       (equivalent-reflexive signed-zero)
       (function/lam
        [['head signed] ['tail vector-type]
         ['tail-zero
          (veq (vector-sup-distance 'tail 'tail) signed-zero)]]
        (let [current-maximum
              (maximum (scalar-distance 'head 'head)
                       (vector-sup-distance 'tail 'tail))
              zero-maximum (maximum signed-zero signed-zero)]
          (equivalent-transitive
           current-maximum zero-maximum signed-zero
           (max-respects
            (scalar-distance 'head 'head)
            (vector-sup-distance 'tail 'tail)
            signed-zero signed-zero
            (app (function/const* 'signed/distance-self-zero []) 'head)
            'tail-zero)
           (function/const* 'signed/absolute-zero []))))
       'values)))})

(def definition-specs
  [signed-map-max-spec vector-sup-distance-spec within-spec])
(def theorem-specs
  [signed-map-max-empty-spec
   signed-equivalent-of-equality-spec
   signed-map-max-cons-spec
   signed-map-max-nonnegative-spec
   signed-map-max-bounded-spec
   signed-map-max-congruent-spec
   vector-sup-distance-empty-left-spec
   vector-sup-distance-empty-right-spec
   vector-sup-distance-cons-spec
   vector-sup-distance-nonnegative-spec
   vector-sup-distance-cons-bounded-spec
   vector-sup-distance-bounded-spec
   vector-sup-distance-cons-symmetric-spec
   vector-sup-distance-empty-symmetric-spec
   vector-sup-distance-cons-empty-symmetric-spec
   vector-sup-distance-cons-symmetric-all-spec
   vector-sup-distance-symmetric-spec
   vector-sup-distance-self-zero-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distance])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-vector-sup-distance (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.vector-sup-distance))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
