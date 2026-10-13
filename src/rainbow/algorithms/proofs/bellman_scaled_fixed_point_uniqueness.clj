(ns rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness
  "Constructive uniqueness of scaled fixed points for finite Bellman numerators."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.nat.distance-core :as distance-core]
            [rainbow.math.nat.metric-separation :as nat-metric]
            [rainbow.math.finite.metric-separation :as finite-metric]
            [rainbow.math.logic.strict-contraction-uniqueness :as contraction]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- recursive-max [left right]
  (function/app (function/const* 'nat/recursive-max []) left right))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- nil-list [element]
  (function/app (function/const* 'data/nil [data-level]) element))

(defn- cons-list [element head tail]
  (function/app (function/const* 'data/cons [data-level])
                element head tail))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [U])
                element source value))

(defn- map-max [element mapping source]
  (function/app (function/const* 'list/nat-map-max [U])
                element mapping source))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- finite-sup-distance [element source left right]
  (function/app (function/const* 'metric/finite-sup-distance [U])
                element source left right))

(defn- rows-normalized [element scale source transition]
  (function/app (function/const* 'markov/rows-normalized-at [U])
                element scale source transition))

(defn- bellman
  [element scale source transition reward discount value state]
  (function/app
   (function/const* 'bellman/fixed-policy-numerator [U])
   element scale source transition reward discount value state))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- nat-equality [left right]
  (equality type-level nat left right))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level])
                carrier value))

(defn- symmetric [level carrier left right same]
  (function/app (function/const* 'equality/symmetric [level])
                carrier left right same))

(defn- transitive [level carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [level])
                carrier left middle right first second))

(defn- congruent
  [source-level target-level source target mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [source-level target-level])
   source target mapping left right same))

(defn- substitute [level carrier left right same predicate at-left]
  (function/app (function/const* 'equality/substitution [level])
                carrier left right same predicate at-left))

(defn- reverse-substitute
  [level carrier left right same predicate at-right]
  (function/app (function/const* 'equality/reverse-substitution [level])
                carrier left right same predicate at-right))

(defn- impossible [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))

(defn- swap-addends [left right tail]
  (let [start (add left (add right tail))
        associated (add (add left right) tail)
        swapped (add (add right left) tail)
        finish (add right (add left tail))
        unassociate
        (symmetric
         type-level nat associated start
         (function/app (function/const* 'nat/add-associative [])
                       left right tail))
        commute
        (congruent
         type-level type-level nat nat
         (function/lam [['value nat]] (add 'value tail))
         (add left right) (add right left)
         (function/app (function/const* 'nat/add-commutative [])
                       left right))
        reassociate
        (function/app (function/const* 'nat/add-associative [])
                      right left tail)
        first-two
        (transitive type-level nat start associated swapped
                    unassociate commute)]
    (transitive type-level nat start swapped finish
                first-two reassociate)))

(def at-most-antisymmetric-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]
           ['left-right (at-most 'left 'right)]
           ['right-left (at-most 'right 'left)]]
          (nat-equality 'left 'right)))]
    {:name 'nat/at-most-antisymmetric
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]
       ['left-right (at-most 'left 'right)]
       ['right-left (at-most 'right 'left)]]
      (nat-equality 'left 'right))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]
         ['ignored (at-most zero 'right)]
         ['right-zero (at-most 'right zero)]]
        (symmetric
         type-level nat 'right zero
         (function/app
          (function/const* 'nat/equal-zero-of-at-most-zero [])
          'right 'right-zero)))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/forall
           [['left-right
             (at-most (succ 'left-previous) 'candidate)]
            ['right-left
             (at-most 'candidate (succ 'left-previous))]]
           (nat-equality (succ 'left-previous) 'candidate)))
         (function/lam
          [['left-zero (at-most (succ 'left-previous) zero)]
           ['ignored (at-most zero (succ 'left-previous))]]
          (function/app
           (function/const* 'nat/equal-zero-of-at-most-zero [])
           (succ 'left-previous) 'left-zero))
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['left-right
               (at-most (succ 'left-previous) 'right-previous)]
              ['right-left
               (at-most 'right-previous (succ 'left-previous))]]
             (nat-equality (succ 'left-previous) 'right-previous))]
           ['left-right
            (at-most (succ 'left-previous) (succ 'right-previous))]
           ['right-left
            (at-most (succ 'right-previous) (succ 'left-previous))]]
          (let [predecessor-left-right
                (function/app
                 (function/const* 'proposition/use-witness [type-level])
                 nat
                 (function/lam
                  [['extra nat]]
                  (nat-equality
                   (add (succ 'left-previous) 'extra)
                   (succ 'right-previous)))
                 (at-most 'left-previous 'right-previous)
                 'left-right
                 (function/lam
                  [['extra nat]
                   ['same
                    (nat-equality
                     (add (succ 'left-previous) 'extra)
                     (succ 'right-previous))]]
                  (function/app
                   (function/const* 'proposition/witness [type-level])
                   nat
                   (function/lam
                    [['gap nat]]
                    (nat-equality
                     (add 'left-previous 'gap) 'right-previous))
                   'extra
                   (function/app
                    (function/const* 'nat/successor-injective [])
                    (add 'left-previous 'extra) 'right-previous 'same))))
                predecessor-right-left
                (function/app
                 (function/const* 'proposition/use-witness [type-level])
                 nat
                 (function/lam
                  [['extra nat]]
                  (nat-equality
                   (add (succ 'right-previous) 'extra)
                   (succ 'left-previous)))
                 (at-most 'right-previous 'left-previous)
                 'right-left
                 (function/lam
                  [['extra nat]
                   ['same
                    (nat-equality
                     (add (succ 'right-previous) 'extra)
                     (succ 'left-previous))]]
                  (function/app
                   (function/const* 'proposition/witness [type-level])
                   nat
                   (function/lam
                    [['gap nat]]
                    (nat-equality
                     (add 'right-previous 'gap) 'left-previous))
                   'extra
                   (function/app
                    (function/const* 'nat/successor-injective [])
                    (add 'right-previous 'extra) 'left-previous 'same))))]
            (congruent
             type-level type-level nat nat
             (function/lam [['value nat]] (succ 'value))
             'left-previous 'right-previous
             (function/app 'induction-hypothesis
                           'right-previous
                           predecessor-left-right
                           predecessor-right-left))))
         'right))
       'left))}))

(def at-most-strict-below-transitive-spec
  {:name 'nat/at-most-strict-below-transitive
   :universes []
   :type
   (function/forall
    [['left nat] ['middle nat] ['right nat]
     ['first (at-most 'left 'middle)]
     ['second (below 'middle 'right)]]
    (below 'left 'right))
   :value
   (function/lam
    [['left nat] ['middle nat] ['right nat]
     ['first (at-most 'left 'middle)]
     ['second (below 'middle 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['first-extra nat]]
      (nat-equality (add 'left 'first-extra) 'middle))
     (below 'left 'right) 'first
     (function/lam
      [['first-extra nat]
       ['same-first
        (nat-equality (add 'left 'first-extra) 'middle)]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat
       (function/lam
        [['second-extra nat]]
        (nat-equality (add (succ 'middle) 'second-extra) 'right))
       (below 'left 'right) 'second
       (function/lam
        [['second-extra nat]
         ['same-second
          (nat-equality
           (add (succ 'middle) 'second-extra) 'right)]]
        (let [combined (add 'first-extra 'second-extra)
              start (add (succ 'left) combined)
              associated
              (add (succ (add 'left 'first-extra)) 'second-extra)
              replaced (add (succ 'middle) 'second-extra)
              reassociate
              (congruent
               type-level type-level nat nat
               (function/lam [['value nat]] (succ 'value))
               (add 'left (add 'first-extra 'second-extra))
               (add (add 'left 'first-extra) 'second-extra)
               (symmetric
                type-level nat
                (add (add 'left 'first-extra) 'second-extra)
                (add 'left (add 'first-extra 'second-extra))
                (function/app
                 (function/const* 'nat/add-associative [])
                 'left 'first-extra 'second-extra)))
              replace-first
              (congruent
               type-level type-level nat nat
               (function/lam
                [['value nat]] (add (succ 'value) 'second-extra))
               (add 'left 'first-extra) 'middle 'same-first)
              first-two
              (transitive type-level nat start associated replaced
                          reassociate replace-first)
              complete
              (transitive type-level nat start replaced 'right
                          first-two 'same-second)]
          (function/app
           (function/const* 'proposition/witness [type-level])
           nat
           (function/lam
            [['extra nat]]
            (nat-equality (add (succ 'left) 'extra) 'right))
           combined complete)))))))})

(def positive-right-of-strict-below-spec
  {:name 'nat/positive-right-of-strict-below
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['ordered (below 'left 'right)]]
    (below zero 'right))
   :value
   (function/lam
    [['left nat] ['right nat] ['ordered (below 'left 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['extra nat]]
      (nat-equality (add (succ 'left) 'extra) 'right))
     (below zero 'right) 'ordered
     (function/lam
      [['extra nat]
       ['same (nat-equality (add (succ 'left) 'extra) 'right)]]
      (function/app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam
        [['positive-extra nat]]
        (nat-equality (add (succ zero) 'positive-extra) 'right))
       (add 'left 'extra) 'same))))})

(def multiply-right-strict-monotone-positive-spec
  {:name 'nat/multiply-right-strict-monotone-positive
   :universes []
   :type
   (function/forall
    [['factor nat] ['left nat] ['right nat]
     ['ordered (below 'left 'right)]
     ['factor-positive (below zero 'factor)]]
    (below (multiply 'left 'factor) (multiply 'right 'factor)))
   :value
   (function/lam
    [['factor nat] ['left nat] ['right nat]
     ['ordered (below 'left 'right)]
     ['factor-positive (below zero 'factor)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['gap nat]]
      (nat-equality (add (succ 'left) 'gap) 'right))
     (below (multiply 'left 'factor) (multiply 'right 'factor))
     'ordered
     (function/lam
      [['gap nat]
       ['same-order
        (nat-equality (add (succ 'left) 'gap) 'right)]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat
       (function/lam
        [['factor-previous nat]]
        (nat-equality
         (add (succ zero) 'factor-previous) 'factor))
       (below (multiply 'left 'factor) (multiply 'right 'factor))
       'factor-positive
       (function/lam
        [['factor-previous nat]
         ['same-factor
          (nat-equality
           (add (succ zero) 'factor-previous) 'factor)]]
        (let [left-product (multiply 'left 'factor)
              gap-product (multiply 'gap 'factor)
              delta (add 'factor-previous gap-product)
              start (add (succ left-product) delta)
              reordered
              (add (succ 'factor-previous)
                   (add left-product gap-product))
              factor-replaced
              (add 'factor (add left-product gap-product))
              combined
              (add 'factor (multiply (add 'left 'gap) 'factor))
              exposed
              (multiply (add (succ 'left) 'gap) 'factor)
              finish (multiply 'right 'factor)
              reorder
              (congruent
               type-level type-level nat nat
               (function/lam [['value nat]] (succ 'value))
               (add left-product
                    (add 'factor-previous gap-product))
               (add 'factor-previous
                    (add left-product gap-product))
               (swap-addends left-product 'factor-previous gap-product))
              replace-factor
              (congruent
               type-level type-level nat nat
               (function/lam
                [['value nat]]
                (add 'value (add left-product gap-product)))
               (succ 'factor-previous) 'factor 'same-factor)
              combine-products
              (congruent
               type-level type-level nat nat
               (function/lam [['value nat]] (add 'factor 'value))
               (add left-product gap-product)
               (multiply (add 'left 'gap) 'factor)
               (symmetric
                type-level nat
                (multiply (add 'left 'gap) 'factor)
                (add left-product gap-product)
                (function/app
                 (function/const* 'nat/multiply-add-left [])
                 'left 'gap 'factor)))
              expose-successor
              (reflexive type-level nat combined)
              replace-right
              (congruent
               type-level type-level nat nat
               (function/lam [['value nat]] (multiply 'value 'factor))
               (add (succ 'left) 'gap) 'right 'same-order)
              first-two
              (transitive type-level nat start reordered factor-replaced
                          reorder replace-factor)
              first-three
              (transitive type-level nat start factor-replaced combined
                          first-two combine-products)
              first-four
              (transitive type-level nat start combined exposed
                          first-three expose-successor)
              complete
              (transitive type-level nat start exposed finish
                          first-four replace-right)]
          (function/app
           (function/const* 'proposition/witness [type-level])
           nat
           (function/lam
            [['extra nat]]
            (nat-equality
             (add (succ left-product) 'extra) finish))
           delta complete)))))))})

(def recursive-max-multiply-left-spec
  {:name 'nat/recursive-max-multiply-left
   :universes []
   :type
   (function/forall
    [['factor nat] ['left nat] ['right nat]]
    (nat-equality
     (recursive-max (multiply 'factor 'left)
                    (multiply 'factor 'right))
     (multiply 'factor (recursive-max 'left 'right))))
   :value
   (function/lam
    [['factor nat] ['left nat] ['right nat]]
    (let [maximum (recursive-max 'left 'right)
          scaled-left (multiply 'factor 'left)
          scaled-right (multiply 'factor 'right)
          scaled-maximum (recursive-max scaled-left scaled-right)
          factor-maximum (multiply 'factor maximum)
          scaled-at-most-factor
          (function/app
           (function/const* 'nat/recursive-max-least-upper-bound [])
           scaled-left scaled-right factor-maximum
           (function/app
            (function/const* 'nat/multiply-left-monotone [])
            'factor 'left maximum
            (function/app
             (function/const* 'nat/recursive-max-left-bound [])
             'left 'right))
           (function/app
            (function/const* 'nat/multiply-left-monotone [])
            'factor 'right maximum
            (function/app
             (function/const* 'nat/recursive-max-right-bound [])
             'left 'right)))
          maximum-is-side
          (function/app
           (function/const* 'nat/recursive-max-is-left-or-right [])
           'left 'right)
          factor-at-most-scaled
          (function/app
           (function/const* 'proposition/use-disjunction [])
           (nat-equality maximum 'left)
           (nat-equality maximum 'right)
           (at-most factor-maximum scaled-maximum)
           maximum-is-side
           (function/lam
            [['maximum-is-left (nat-equality maximum 'left)]]
            (reverse-substitute
             type-level nat factor-maximum scaled-left
             (congruent
              type-level type-level nat nat
              (function/lam
               [['value nat]] (multiply 'factor 'value))
              maximum 'left 'maximum-is-left)
             (function/lam
              [['candidate nat]] (at-most 'candidate scaled-maximum))
             (function/app
              (function/const* 'nat/recursive-max-left-bound [])
              scaled-left scaled-right)))
           (function/lam
            [['maximum-is-right (nat-equality maximum 'right)]]
            (reverse-substitute
             type-level nat factor-maximum scaled-right
             (congruent
              type-level type-level nat nat
              (function/lam
               [['value nat]] (multiply 'factor 'value))
              maximum 'right 'maximum-is-right)
             (function/lam
              [['candidate nat]] (at-most 'candidate scaled-maximum))
             (function/app
              (function/const* 'nat/recursive-max-right-bound [])
              scaled-left scaled-right))))]
      (function/app
       (function/const* 'nat/at-most-antisymmetric [])
       scaled-maximum factor-maximum
       scaled-at-most-factor factor-at-most-scaled)))})

(def list-map-max-multiply-left-spec
  (let [scaled-mapping
        (function/lam
         [['value 'A]]
         (multiply 'factor (function/app 'mapping 'value)))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (nat-equality
          (map-max 'A scaled-mapping 'source)
          (multiply 'factor (map-max 'A 'mapping 'source))))]
    {:name 'list/nat-map-max-multiply-left
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['factor nat]
       ['mapping (function/arrow 'A nat)]
       ['source (list-of 'A)]]
      (nat-equality
       (map-max 'A scaled-mapping 'source)
       (multiply 'factor (map-max 'A 'mapping 'source))))
     :value
     (function/lam
      [['A type-u]
       ['factor nat]
       ['mapping (function/arrow 'A nat)]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (symmetric
        type-level nat (multiply 'factor zero) zero
        (function/app (function/const* 'nat/times-zero []) 'factor))
       (function/lam
        [['head 'A]
         ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [head-value (function/app 'mapping 'head)
              tail-maximum (map-max 'A 'mapping 'tail)
              scaled-head (multiply 'factor head-value)
              scaled-tail (map-max 'A scaled-mapping 'tail)
              factor-tail (multiply 'factor tail-maximum)
              start (recursive-max scaled-head scaled-tail)
              middle (recursive-max scaled-head factor-tail)
              finish
              (multiply 'factor
                        (recursive-max head-value tail-maximum))
              replace-tail
              (congruent
               type-level type-level nat nat
               (function/lam
                [['value nat]] (recursive-max scaled-head 'value))
               scaled-tail factor-tail 'induction-hypothesis)
              distribute-maximum
              (function/app
               (function/const* 'nat/recursive-max-multiply-left [])
               'factor head-value tail-maximum)]
          (transitive type-level nat start middle finish
                      replace-tail distribute-maximum)))
       'source))}))

(def finite-sup-distance-multiply-left-spec
  (let [scaled
        (fn [mapping]
          (function/lam
           [['state 'A]]
           (multiply 'factor (function/app mapping 'state))))
        original-distance-mapping
        (function/lam
         [['state 'A]]
         (distance (function/app 'left 'state)
                   (function/app 'right 'state)))
        scaled-distance-mapping
        (function/lam
         [['state 'A]]
         (distance (function/app (scaled 'left) 'state)
                   (function/app (scaled 'right) 'state)))
        multiplied-distance-mapping
        (function/lam
         [['state 'A]]
         (multiply
          'factor
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))))]
    {:name 'metric/finite-sup-distance-multiply-left
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['source (exact-finset-of 'A)]
       ['factor nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (nat-equality
       (finite-sup-distance 'A 'source (scaled 'left) (scaled 'right))
       (multiply
        'factor (finite-sup-distance 'A 'source 'left 'right))))
     :value
     (function/lam
      [['A type-u]
       ['source (exact-finset-of 'A)]
       ['factor nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (let [source-list (enumeration 'A 'source)
            start (map-max 'A scaled-distance-mapping source-list)
            middle
            (map-max 'A multiplied-distance-mapping source-list)
            finish
            (multiply 'factor
                      (map-max 'A original-distance-mapping source-list))
            expose-pointwise-scale
            (function/app
             (function/const* 'list/nat-map-max-congruent [U])
             'A scaled-distance-mapping multiplied-distance-mapping
             (function/lam
              [['state 'A]]
              (function/app
               (function/const* 'nat/distance-multiply-left [])
               'factor
               (function/app 'left 'state)
               (function/app 'right 'state)))
             source-list)
            distribute-maximum
            (function/app
             (function/const* 'list/nat-map-max-multiply-left [U])
             'A 'factor original-distance-mapping source-list)]
        (transitive type-level nat start middle finish
                    expose-pointwise-scale distribute-maximum)))}))

(defn- scaled-contraction-context []
  (let [value-space (function/arrow 'A nat)
        scale-square (multiply 'scale 'scale)
        scaled
        (fn [mapping]
          (function/lam
           [['state 'A]]
           (multiply scale-square (function/app mapping 'state))))
        sup-distance
        (fn [left right]
          (finite-sup-distance 'A 'source left right))
        transform-at
        (fn [value] (function/app 'transform value))]
    {:binders
     [['A type-u]
      ['source (exact-finset-of 'A)]
      ['scale nat]
      ['discount nat]
      ['transform (function/arrow value-space value-space)]
      ['left value-space]
      ['right value-space]
      ['discount-below-scale (below 'discount 'scale)]
      ['contractive-bound
       (function/forall
        [['candidate-left value-space]
         ['candidate-right value-space]]
        (at-most
         (sup-distance (transform-at 'candidate-left)
                       (transform-at 'candidate-right))
         (multiply
          'discount
          (multiply
           'scale
           (sup-distance 'candidate-left 'candidate-right)))))]
      ['left-scaled-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (transform-at 'left) 'state)
         (function/app (scaled 'left) 'state)))]
      ['right-scaled-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (transform-at 'right) 'state)
         (function/app (scaled 'right) 'state)))]]
     :scale-square scale-square
     :scaled scaled
     :sup-distance sup-distance
     :transform-at transform-at}))

(def scaled-contraction-scaled-fixed-points-have-zero-sup-distance-spec
  (let [{:keys [binders scale-square scaled sup-distance transform-at]}
        (scaled-contraction-context)
        original-distance (sup-distance 'left 'right)
        output-distance
        (sup-distance (transform-at 'left) (transform-at 'right))
        scale-times-distance (multiply 'scale original-distance)
        contraction-bound (multiply 'discount scale-times-distance)
        scaled-distance (multiply scale-square original-distance)
        associated-scaled-distance
        (multiply 'scale scale-times-distance)]
    {:name
     'metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance
     :universes ['u]
     :type
     (function/forall binders (nat-equality original-distance zero))
     :value
     (function/lam
      binders
      (function/app
       (function/const* 'nat/equal-zero-of-not-positive [])
       original-distance
       (function/lam
        [['positive (below zero original-distance)]]
        (let [positive-scale
              (function/app
               (function/const* 'nat/positive-right-of-strict-below [])
               'discount 'scale 'discount-below-scale)
              positive-scale-times-distance
              (function/app
               (function/const*
                'nat/multiply-right-strict-monotone-positive [])
               original-distance zero 'scale
               positive-scale 'positive)
              bound-below-associated-scaled
              (function/app
               (function/const*
                'nat/multiply-right-strict-monotone-positive [])
               scale-times-distance 'discount 'scale
               'discount-below-scale positive-scale-times-distance)
              scale-associative
              (function/app
               (function/const* 'nat/multiply-associative [])
               'scale 'scale original-distance)
              bound-below-scaled
              (reverse-substitute
               type-level nat scaled-distance associated-scaled-distance
               scale-associative
               (function/lam
                [['upper nat]] (below contraction-bound 'upper))
               bound-below-associated-scaled)
              output-at-most-bound
              (function/app 'contractive-bound 'left 'right)
              output-below-scaled
              (function/app
               (function/const*
                'nat/at-most-strict-below-transitive [])
               output-distance contraction-bound scaled-distance
               output-at-most-bound bound-below-scaled)
              fixed-distance
              (function/app
               (function/const* 'metric/finite-sup-congruent-on [U])
               'A 'source
               (transform-at 'left) (transform-at 'right)
               (scaled 'left) (scaled 'right)
               'left-scaled-fixed 'right-scaled-fixed)
              expose-scale
              (function/app
               (function/const*
                'metric/finite-sup-distance-multiply-left [U])
               'A 'source scale-square 'left 'right)
              output-equals-scaled
              (transitive
               type-level nat output-distance
               (sup-distance (scaled 'left) (scaled 'right))
               scaled-distance fixed-distance expose-scale)
              self-below
              (substitute
               type-level nat output-distance scaled-distance
               output-equals-scaled
               (function/lam
                [['candidate nat]] (below 'candidate scaled-distance))
               output-below-scaled)]
          (function/app
           (function/const* 'nat/not-strictly-below-self [])
           scaled-distance self-below)))))}))

(defn- bellman-context []
  (let [value-space (function/arrow 'A nat)
        scale-square (multiply 'scale 'scale)
        bellman-at
        (fn [value]
          (function/lam
           [['state 'A]]
           (bellman 'A 'scale 'source 'transition 'reward
                    'discount value 'state)))
        scaled
        (fn [value]
          (function/lam
           [['state 'A]]
           (multiply scale-square (function/app value 'state))))]
    {:binders
     [['A type-u]
      ['scale nat]
      ['source (exact-finset-of 'A)]
      ['transition (function/arrow 'A 'A nat)]
      ['reward (function/arrow 'A nat)]
      ['discount nat]
      ['normalized (rows-normalized 'A 'scale 'source 'transition)]
      ['discount-below-scale (below 'discount 'scale)]
      ['left value-space]
      ['right value-space]
      ['left-scaled-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (bellman-at 'left) 'state)
         (function/app (scaled 'left) 'state)))]
      ['right-scaled-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (bellman-at 'right) 'state)
         (function/app (scaled 'right) 'state)))]]
     :bellman-at bellman-at
     :scaled scaled}))

(def fixed-policy-scaled-fixed-points-have-zero-sup-distance-spec
  (let [{:keys [binders bellman-at]} (bellman-context)]
    {:name
     'bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance
     :universes ['u]
     :type
     (function/forall
      binders
      (nat-equality
       (finite-sup-distance 'A 'source 'left 'right) zero))
     :value
     (function/lam
      binders
      (function/app
       (function/const*
        'metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance
        [U])
       'A 'source 'scale 'discount
       (function/lam
        [['value (function/arrow 'A nat)]]
        (bellman-at 'value))
       'left 'right 'discount-below-scale
       (function/lam
        [['candidate-left (function/arrow 'A nat)]
         ['candidate-right (function/arrow 'A nat)]]
        (function/app
         (function/const* 'bellman/fixed-policy-sup-contraction [U])
         'A 'scale 'source 'transition 'reward 'discount
         'candidate-left 'candidate-right 'normalized))
       'left-scaled-fixed 'right-scaled-fixed))}))

(def fixed-policy-scaled-fixed-points-unique-on-support-spec
  (let [{:keys [binders]} (bellman-context)]
    {:name 'bellman/fixed-policy-scaled-fixed-points-unique-on-support
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (nat-equality (function/app 'left 'state)
                     (function/app 'right 'state))))
     :value
     (function/lam
      binders
      (function/lam
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (function/app
        (function/const* 'metric/pointwise-equal-of-finite-sup-zero [U])
        'A 'source 'left 'right
        (function/app
         (function/const*
          'bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance
          [U])
         'A 'scale 'source 'transition 'reward 'discount
         'normalized 'discount-below-scale 'left 'right
         'left-scaled-fixed 'right-scaled-fixed)
        'state 'member)))}))

(def theorem-specs
  [at-most-antisymmetric-spec
   at-most-strict-below-transitive-spec
   positive-right-of-strict-below-spec
   multiply-right-strict-monotone-positive-spec
   recursive-max-multiply-left-spec
   list-map-max-multiply-left-spec
   finite-sup-distance-multiply-left-spec
   scaled-contraction-scaled-fixed-points-have-zero-sup-distance-spec
   fixed-policy-scaled-fixed-points-have-zero-sup-distance-spec
   fixed-policy-scaled-fixed-points-unique-on-support-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Bellman scaled uniqueness expression failed elaboration"
                {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native
           :producer :constructive-bellman-scaled-fixed-point-uniqueness}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Bellman scaled uniqueness theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

;; Installs the chain these proofs use, in dependency order, so the module installs on any base that has the
;; natural numbers (as the milestone checkpoint did implicitly).
(defn extend-environment [checked-environment]
  (reduce add-spec
          (-> checked-environment
              distance-core/extend-environment
              nat-metric/extend-environment
              finite-metric/extend-environment
              contraction/extend-environment)
          theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
