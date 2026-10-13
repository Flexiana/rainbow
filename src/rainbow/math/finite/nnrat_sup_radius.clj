(ns rainbow.math.finite.nnrat-sup-radius
  "A Bellman-compatible NNRAT supremum radius over exact finite carriers.

  Unlike the signed-valued metric view, this fold stays in NNRAT, so its result
  can be supplied directly as the epsilon parameter of Rainbow's finite Bellman
  contraction theorems.  It maps each enumerated state to the exact
  `nnrat/distance` of the two values and folds with the decidable NNRAT maximum.

  The package proves the two directions a residual certificate needs: every
  member distance is below the finite radius, and any uniform pointwise bound
  bounds the radius.  Nonnegativity is structural from the zero base.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distance :as distance]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

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
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- maximum [left right]
  (app (function/const* 'minmax/max []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- map-max [element mapping source]
  (app (function/const* 'list/nnrat-map-max [U])
       element mapping source))
(defn- finite-radius [element source left right]
  (app (function/const* 'metric/finite-nnrat-sup-radius [U])
       element source left right))
(defn- order-reflexive [value]
  (app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- max-left [left right]
  (app (function/const* 'minmax/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'minmax/max-upper-right []) left right))
(defn- max-below [left right upper left-bound right-bound]
  (app (function/const* 'minmax/at-most-max [])
       left right upper left-bound right-bound))

(def nnrat-map-max-spec
  {:name 'list/nnrat-map-max
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A nnrat)]]
    (function/arrow (list-of 'A) nnrat))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A nnrat)]
     ['source (list-of 'A)]]
    (app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] nnrat)
     nnrat-zero
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-maximum nnrat]]
      (maximum (app 'mapping 'head) 'tail-maximum))
     'source))})

(def finite-nnrat-sup-radius-spec
  {:name 'metric/finite-nnrat-sup-radius
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    nnrat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (map-max
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'left 'state) (app 'right 'state)))
     (enumeration 'A 'source)))})

(def nnrat-map-max-upper-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (rle (app 'mapping 'value)
               (map-max 'A 'mapping 'source))))]
    {:name 'list/nnrat-map-max-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A nnrat)]
       ['source (list-of 'A)] ['value 'A]
       ['member (membership 'A 'source 'value)]]
      (rle (app 'mapping 'value)
           (map-max 'A 'mapping 'source)))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A nnrat)]
       ['source (list-of 'A)]]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['value 'A]
         ['impossible (membership 'A (nil-list 'A) 'value)]]
        (app (function/const* 'proposition/explode [])
             (rle (app 'mapping 'value) nnrat-zero)
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
              target (rle (app 'mapping 'value)
                          (maximum head-value tail-maximum))]
          (app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (app
             (function/const* 'equality/substitution [data-level])
             'A 'head 'value
             (app (function/const* 'equality/symmetric [data-level])
                  'A 'value 'head 'same)
             (function/lam
              [['candidate 'A]]
              (rle (app 'mapping 'candidate)
                   (maximum head-value tail-maximum)))
             (max-left head-value tail-maximum)))
           (function/lam
            [['tail-member tail-case]]
            (order-transitive
             (app 'mapping 'value) tail-maximum
             (maximum head-value tail-maximum)
             (app 'induction-hypothesis 'value 'tail-member)
             (max-right head-value tail-maximum))))))
       'source))}))

(def nnrat-map-max-bounded-spec
  (let [bounded
        (fn [mapping upper source]
          (function/forall
           [['value 'A] ['member (membership 'A source 'value)]]
           (rle (app mapping 'value) upper)))]
    {:name 'list/nnrat-map-max-bounded
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A nnrat)]
       ['upper nnrat] ['zero-upper (rle nnrat-zero 'upper)]
       ['source (list-of 'A)]
       ['pointwise (bounded 'mapping 'upper 'source)]]
      (rle (map-max 'A 'mapping 'source) 'upper))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A nnrat)]
       ['upper nnrat] ['zero-upper (rle nnrat-zero 'upper)]
       ['source (list-of 'A)]]
      (let [motive
            (function/lam
             [['current (list-of 'A)]]
             (function/arrow
              (bounded 'mapping 'upper 'current)
              (rle (map-max 'A 'mapping 'current) 'upper)))]
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
             (rle (map-max 'A 'mapping 'tail) 'upper))]
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

(def nnrat-map-max-nonnegative-spec
  {:name 'list/nnrat-map-max-nonnegative
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A nnrat)]
     ['source (list-of 'A)]]
    (rle nnrat-zero (map-max 'A 'mapping 'source)))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A nnrat)]
     ['source (list-of 'A)]]
    (let [motive
          (function/lam
           [['current (list-of 'A)]]
           (rle nnrat-zero (map-max 'A 'mapping 'current)))]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (order-reflexive nnrat-zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['tail-nonnegative
          (rle nnrat-zero (map-max 'A 'mapping 'tail))]]
        (order-transitive
         nnrat-zero
         (map-max 'A 'mapping 'tail)
         (maximum (app 'mapping 'head)
                  (map-max 'A 'mapping 'tail))
         'tail-nonnegative
         (max-right (app 'mapping 'head)
                    (map-max 'A 'mapping 'tail))))
       'source)))})

(def finite-nnrat-sup-radius-upper-bound-spec
  (let [pointwise
        (function/lam
         [['state 'A]]
         (scalar-distance (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-nnrat-sup-radius-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (rle (scalar-distance (app 'left 'state) (app 'right 'state))
           (finite-radius 'A 'source 'left 'right)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (app (function/const* 'list/nnrat-map-max-upper-bound [U])
           'A pointwise (enumeration 'A 'source) 'state 'member))}))

(def finite-nnrat-sup-radius-bounded-spec
  (let [pointwise-distance
        (function/lam
         [['state 'A]]
         (scalar-distance (app 'left 'state) (app 'right 'state)))]
    {:name 'metric/finite-nnrat-sup-radius-bounded
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['upper nnrat] ['zero-upper (rle nnrat-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (rle (scalar-distance (app 'left 'state) (app 'right 'state))
              'upper))]]
      (rle (finite-radius 'A 'source 'left 'right) 'upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['upper nnrat] ['zero-upper (rle nnrat-zero 'upper)]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (rle (scalar-distance (app 'left 'state) (app 'right 'state))
              'upper))]]
      (app (function/const* 'list/nnrat-map-max-bounded [U])
           'A pointwise-distance 'upper 'zero-upper
           (enumeration 'A 'source)
           (function/lam
            [['state 'A]
             ['member
              (membership 'A (enumeration 'A 'source) 'state)]]
            (app 'pointwise 'state 'member))))}))

(def finite-nnrat-sup-radius-nonnegative-spec
  {:name 'metric/finite-nnrat-sup-radius-nonnegative
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (rle nnrat-zero (finite-radius 'A 'source 'left 'right)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]]
    (app
     (function/const* 'list/nnrat-map-max-nonnegative [U])
     'A
     (function/lam
      [['state 'A]]
      (scalar-distance (app 'left 'state) (app 'right 'state)))
     (enumeration 'A 'source)))})

(def definition-specs
  [nnrat-map-max-spec finite-nnrat-sup-radius-spec])

(def theorem-specs
  [nnrat-map-max-upper-bound-spec
   nnrat-map-max-bounded-spec
   nnrat-map-max-nonnegative-spec
   finite-nnrat-sup-radius-upper-bound-spec
   finite-nnrat-sup-radius-bounded-spec
   finite-nnrat-sup-radius-nonnegative-spec])

(defn extend-environment [env]
  (-> env
      distance/extend-environment
      minmax/extend-environment
      (support/extend-with :finite-nnrat-sup-radius
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
