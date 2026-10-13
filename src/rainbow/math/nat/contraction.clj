(ns rainbow.math.nat.contraction
  "Natural multiplication laws needed by finite metric contraction proofs."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
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

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- list-length [element source]
  (function/app (function/const* 'list/length [data-level])
                element source))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nat-map-sum [U])
                element mapping source))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- expectation [element source mass value]
  (function/app
   (function/const* 'probability/expectation-numerator [U])
   element source mass value))

(defn- weight-total [element source mass]
  (function/app (function/const* 'probability/weight-total [U])
                element source mass))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(defn- swap-addends [left right tail]
  (let [start (add left (add right tail))
        associated (add (add left right) tail)
        swapped (add (add right left) tail)
        finish (add right (add left tail))
        unassociate
        (symmetric
         associated start
         (function/app (function/const* 'nat/add-associative [])
                       left right tail))
        commute
        (congruent
         (function/lam [['value nat]] (add 'value tail))
         (add left right) (add right left)
         (function/app (function/const* 'nat/add-commutative [])
                       left right))
        reassociate
        (function/app (function/const* 'nat/add-associative [])
                      right left tail)
        first-two
        (transitive start associated swapped unassociate commute)]
    (transitive start swapped finish first-two reassociate)))

(def multiply-successor-right-spec
  (let [motive
        (function/lam
         [['value nat]]
         (function/forall
          [['factor nat]]
          (equality
           (multiply 'value (succ 'factor))
           (add 'value (multiply 'value 'factor)))))]
    {:name 'nat/multiply-successor-right
     :universes []
     :type
     (function/forall
      [['value nat] ['factor nat]]
      (equality
       (multiply 'value (succ 'factor))
       (add 'value (multiply 'value 'factor))))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['factor nat]]
        (function/app (function/const* 'equality/reflexive [type-level])
                      nat zero))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['factor nat]]
        (let [previous-successor (multiply 'previous (succ 'factor))
              previous-product (multiply 'previous 'factor)
              start (add (succ 'factor) previous-successor)
              middle (add (succ 'factor)
                          (add 'previous previous-product))
              finish (add (succ 'previous)
                          (add 'factor previous-product))
              replace-previous
              (congruent
               (function/lam [['value nat]] (add (succ 'factor) 'value))
               previous-successor (add 'previous previous-product)
               (function/app 'induction-hypothesis 'factor))
              reorder
              (congruent
               (function/lam [['value nat]] (succ 'value))
               (add 'factor (add 'previous previous-product))
               (add 'previous (add 'factor previous-product))
               (swap-addends 'factor 'previous previous-product))]
          (transitive start middle finish replace-previous reorder)))
       'value))}))

(def multiply-commutative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (equality (multiply 'left 'right)
                    (multiply 'right 'left))))]
    {:name 'nat/multiply-commutative
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (equality (multiply 'left 'right) (multiply 'right 'left)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (symmetric
         (multiply 'right zero) zero
         (function/app (function/const* 'nat/times-zero []) 'right)))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['right nat]]
        (let [start (add 'right (multiply 'previous 'right))
              middle (add 'right (multiply 'right 'previous))
              finish (multiply 'right (succ 'previous))
              replace
              (congruent
               (function/lam [['value nat]] (add 'right 'value))
               (multiply 'previous 'right) (multiply 'right 'previous)
               (function/app 'induction-hypothesis 'right))
              expose
              (symmetric
               finish middle
               (function/app
                (function/const* 'nat/multiply-successor-right [])
                'right 'previous))]
          (transitive start middle finish replace expose)))
       'left))}))

(def distance-multiply-right-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat] ['factor nat]]
          (equality
           (distance (multiply 'left 'factor) (multiply 'right 'factor))
           (multiply (distance 'left 'right) 'factor))))]
    {:name 'nat/distance-multiply-right
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['factor nat]]
      (equality
       (distance (multiply 'left 'factor) (multiply 'right 'factor))
       (multiply (distance 'left 'right) 'factor)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat] ['factor nat]]
        (function/app (function/const* 'equality/reflexive [type-level])
                      nat (multiply 'right 'factor)))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat] ['factor nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (equality
           (distance (multiply (succ 'left-previous) 'factor)
                     (multiply 'candidate 'factor))
           (multiply (distance (succ 'left-previous) 'candidate) 'factor)))
         (function/app
          (function/const* 'nat/distance-commutative [])
          (multiply (succ 'left-previous) 'factor) zero)
         (function/lam
          [['right-previous nat]
           ['ignored
            (equality
             (distance (multiply (succ 'left-previous) 'factor)
                       (multiply 'right-previous 'factor))
             (multiply (distance (succ 'left-previous) 'right-previous)
                       'factor))]]
          (let [left-product (multiply 'left-previous 'factor)
                right-product (multiply 'right-previous 'factor)
                start (distance (add 'factor left-product)
                                (add 'factor right-product))
                middle (distance left-product right-product)
                finish
                (multiply (distance 'left-previous 'right-previous) 'factor)]
            (transitive
             start middle finish
             (function/app (function/const* 'nat/distance-add-left [])
                           'factor left-product right-product)
             (function/app 'induction-hypothesis
                           'right-previous 'factor))))
         'right))
       'left))}))

(def distance-multiply-left-spec
  {:name 'nat/distance-multiply-left
   :universes []
   :type
   (function/forall
    [['factor nat] ['left nat] ['right nat]]
    (equality
     (distance (multiply 'factor 'left) (multiply 'factor 'right))
     (multiply 'factor (distance 'left 'right))))
   :value
   (function/lam
    [['factor nat] ['left nat] ['right nat]]
    (let [start
          (distance (multiply 'factor 'left) (multiply 'factor 'right))
          first-middle
          (distance (multiply 'left 'factor) (multiply 'factor 'right))
          second-middle
          (distance (multiply 'left 'factor) (multiply 'right 'factor))
          third-middle (multiply (distance 'left 'right) 'factor)
          finish (multiply 'factor (distance 'left 'right))
          commute-left
          (congruent
           (function/lam
            [['value nat]] (distance 'value (multiply 'factor 'right)))
           (multiply 'factor 'left) (multiply 'left 'factor)
           (function/app (function/const* 'nat/multiply-commutative [])
                         'factor 'left))
          commute-right
          (congruent
           (function/lam
            [['value nat]] (distance (multiply 'left 'factor) 'value))
           (multiply 'factor 'right) (multiply 'right 'factor)
           (function/app (function/const* 'nat/multiply-commutative [])
                         'factor 'right))
          distance-product
          (function/app (function/const* 'nat/distance-multiply-right [])
                        'left 'right 'factor)
          commute-result
          (function/app (function/const* 'nat/multiply-commutative [])
                        (distance 'left 'right) 'factor)
          first-two
          (transitive start first-middle second-middle
                      commute-left commute-right)
          first-three
          (transitive start second-middle third-middle
                      first-two distance-product)]
      (transitive start third-middle finish
                  first-three commute-result)))})

(def at-most-rewrite-right-spec
  {:name 'nat/at-most-rewrite-right
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['replacement nat]
     ['same (equality 'right 'replacement)]
     ['ordered (at-most 'left 'right)]]
    (at-most 'left 'replacement))
   :value
   (function/lam
    [['left nat] ['right nat] ['replacement nat]
     ['same (equality 'right 'replacement)]
     ['ordered (at-most 'left 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam [['extra nat]]
                   (equality (add 'left 'extra) 'right))
     (at-most 'left 'replacement)
     'ordered
     (function/lam
      [['extra nat]
       ['witness-equality (equality (add 'left 'extra) 'right)]]
      (function/app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam [['candidate-extra nat]]
                     (equality (add 'left 'candidate-extra) 'replacement))
       'extra
       (transitive (add 'left 'extra) 'right 'replacement
                   'witness-equality 'same)))))})

(def list-map-sum-distance-bound-spec
  (let [left-sum (fn [source] (map-sum 'A 'left source))
        right-sum (fn [source] (map-sum 'A 'right source))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (at-most
          (distance (left-sum 'source) (right-sum 'source))
          (multiply (list-length 'A 'source) 'epsilon)))]
    {:name 'list/nat-map-sum-distance-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['value 'A]]
         (at-most
          (distance (function/app 'left 'value)
                    (function/app 'right 'value))
          'epsilon))]
       ['source (list-of 'A)]]
      (at-most
       (distance (left-sum 'source) (right-sum 'source))
       (multiply (list-length 'A 'source) 'epsilon)))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['value 'A]]
         (at-most
          (distance (function/app 'left 'value)
                    (function/app 'right 'value))
          'epsilon))]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app (function/const* 'nat/at-most-reflexive []) zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [left-head (function/app 'left 'head)
              right-head (function/app 'right 'head)
              left-tail (left-sum 'tail)
              right-tail (right-sum 'tail)
              left-total (add left-head left-tail)
              bridge (add right-head left-tail)
              right-total (add right-head right-tail)
              head-distance (distance left-head right-head)
              tail-distance (distance left-tail right-tail)
              triangle-upper
              (add (distance left-total bridge)
                   (distance bridge right-total))
              reduced-upper (add head-distance tail-distance)
              head-reduction
              (function/app
               (function/const* 'nat/distance-add-right [])
               left-head left-tail right-head)
              tail-reduction
              (function/app
               (function/const* 'nat/distance-add-left [])
               right-head left-tail right-tail)
              reduce-head
              (congruent
               (function/lam
                [['value nat]]
                (add 'value (distance bridge right-total)))
               (distance left-total bridge) head-distance head-reduction)
              reduce-tail
              (congruent
               (function/lam [['value nat]] (add head-distance 'value))
               (distance bridge right-total) tail-distance tail-reduction)
              reduced-middle
              (add head-distance (distance bridge right-total))
              reduce-upper
              (transitive triangle-upper reduced-middle reduced-upper
                          reduce-head reduce-tail)
              triangle
              (function/app
               (function/const* 'nat/distance-triangle [])
               left-total bridge right-total)
              triangle-reduced
              (function/app
               (function/const* 'nat/at-most-rewrite-right [])
               (distance left-total right-total)
               triangle-upper reduced-upper reduce-upper triangle)
              component-bound
              (function/app
               (function/const* 'nat/add-monotone [])
               head-distance 'epsilon
               tail-distance (multiply (list-length 'A 'tail) 'epsilon)
               (function/app 'pointwise 'head) 'induction-hypothesis)]
          (function/app
           (function/const* 'nat/at-most-transitive [])
           (distance left-total right-total) reduced-upper
           (add 'epsilon (multiply (list-length 'A 'tail) 'epsilon))
           triangle-reduced component-bound)))
       'source))}))

(def at-most-rewrite-left-spec
  {:name 'nat/at-most-rewrite-left
   :universes []
   :type
   (function/forall
    [['left nat] ['replacement nat] ['right nat]
     ['same (equality 'left 'replacement)]
     ['ordered (at-most 'replacement 'right)]]
    (at-most 'left 'right))
   :value
   (function/lam
    [['left nat] ['replacement nat] ['right nat]
     ['same (equality 'left 'replacement)]
     ['ordered (at-most 'replacement 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam [['extra nat]]
                   (equality (add 'replacement 'extra) 'right))
     (at-most 'left 'right)
     'ordered
     (function/lam
      [['extra nat]
       ['witness-equality (equality (add 'replacement 'extra) 'right)]]
      (let [start (add 'left 'extra)
            middle (add 'replacement 'extra)
            replace-left
            (congruent
             (function/lam [['value nat]] (add 'value 'extra))
             'left 'replacement 'same)]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['candidate-extra nat]]
                       (equality (add 'left 'candidate-extra) 'right))
         'extra
         (transitive start middle 'right
                     replace-left 'witness-equality))))))})

(def list-map-sum-distance-bound-by-spec
  (let [left-sum (fn [source] (map-sum 'A 'left source))
        right-sum (fn [source] (map-sum 'A 'right source))
        bound-sum (fn [source] (map-sum 'A 'bound source))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (at-most
          (distance (left-sum 'source) (right-sum 'source))
          (bound-sum 'source)))]
    {:name 'list/nat-map-sum-distance-bound-by
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['bound (function/arrow 'A nat)]
       ['pointwise
        (function/forall
         [['value 'A]]
         (at-most
          (distance (function/app 'left 'value)
                    (function/app 'right 'value))
          (function/app 'bound 'value)))]
       ['source (list-of 'A)]]
      (at-most
       (distance (left-sum 'source) (right-sum 'source))
       (bound-sum 'source)))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['bound (function/arrow 'A nat)]
       ['pointwise
        (function/forall
         [['value 'A]]
         (at-most
          (distance (function/app 'left 'value)
                    (function/app 'right 'value))
          (function/app 'bound 'value)))]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app (function/const* 'nat/at-most-reflexive []) zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [left-head (function/app 'left 'head)
              right-head (function/app 'right 'head)
              left-tail (left-sum 'tail)
              right-tail (right-sum 'tail)
              left-total (add left-head left-tail)
              bridge (add right-head left-tail)
              right-total (add right-head right-tail)
              head-distance (distance left-head right-head)
              tail-distance (distance left-tail right-tail)
              triangle-upper
              (add (distance left-total bridge)
                   (distance bridge right-total))
              reduced-upper (add head-distance tail-distance)
              reduce-head
              (congruent
               (function/lam
                [['value nat]]
                (add 'value (distance bridge right-total)))
               (distance left-total bridge) head-distance
               (function/app
                (function/const* 'nat/distance-add-right [])
                left-head left-tail right-head))
              reduce-tail
              (congruent
               (function/lam [['value nat]] (add head-distance 'value))
               (distance bridge right-total) tail-distance
               (function/app
                (function/const* 'nat/distance-add-left [])
                right-head left-tail right-tail))
              reduced-middle
              (add head-distance (distance bridge right-total))
              reduce-upper
              (transitive triangle-upper reduced-middle reduced-upper
                          reduce-head reduce-tail)
              triangle-reduced
              (function/app
               (function/const* 'nat/at-most-rewrite-right [])
               (distance left-total right-total)
               triangle-upper reduced-upper reduce-upper
               (function/app
                (function/const* 'nat/distance-triangle [])
                left-total bridge right-total))
              component-bound
              (function/app
               (function/const* 'nat/add-monotone [])
               head-distance (function/app 'bound 'head)
               tail-distance (bound-sum 'tail)
               (function/app 'pointwise 'head) 'induction-hypothesis)]
          (function/app
           (function/const* 'nat/at-most-transitive [])
           (distance left-total right-total) reduced-upper
           (add (function/app 'bound 'head) (bound-sum 'tail))
           triangle-reduced component-bound)))
       'source))}))

(def list-map-sum-multiply-right-spec
  (let [scaled
        (function/lam
         [['value 'A]]
         (multiply (function/app 'mapping 'value) 'factor))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (equality
          (map-sum 'A scaled 'source)
          (multiply (map-sum 'A 'mapping 'source) 'factor)))]
    {:name 'list/nat-map-sum-multiply-right
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A nat)]
       ['factor nat] ['source (list-of 'A)]]
      (equality
       (map-sum
        'A
        (function/lam
         [['value 'A]]
         (multiply (function/app 'mapping 'value) 'factor))
        'source)
       (multiply (map-sum 'A 'mapping 'source) 'factor)))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A nat)]
       ['factor nat] ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app (function/const* 'equality/reflexive [type-level])
                     nat zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [head-value (function/app 'mapping 'head)
              tail-sum (map-sum 'A 'mapping 'tail)
              start
              (add (multiply head-value 'factor)
                   (map-sum 'A scaled 'tail))
              middle
              (add (multiply head-value 'factor)
                   (multiply tail-sum 'factor))
              finish (multiply (add head-value tail-sum) 'factor)
              replace-tail
              (congruent
               (function/lam
                [['value nat]] (add (multiply head-value 'factor) 'value))
               (map-sum 'A scaled 'tail)
               (multiply tail-sum 'factor)
               'induction-hypothesis)
              combine
              (symmetric
               finish middle
               (function/app (function/const* 'nat/multiply-add-left [])
                             head-value tail-sum 'factor))]
          (transitive start middle finish replace-tail combine)))
       'source))}))

(def expectation-distance-bound-spec
  (let [left-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'left 'state)
                   (function/app 'mass 'state)))
        right-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'right 'state)
                   (function/app 'mass 'state)))
        bound-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'mass 'state) 'epsilon))
        source-list (enumeration 'A 'source)
        bound-sum (map-sum 'A bound-weighted source-list)
        finish (multiply (weight-total 'A 'source 'mass) 'epsilon)]
    {:name 'probability/expectation-distance-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['state 'A]]
         (at-most
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))
          'epsilon))]]
      (at-most
       (distance (expectation 'A 'source 'mass 'left)
                 (expectation 'A 'source 'mass 'right))
       (multiply (weight-total 'A 'source 'mass) 'epsilon)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['state 'A]]
         (at-most
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))
          'epsilon))]]
      (let [weighted-pointwise
            (function/lam
             [['state 'A]]
             (let [left-value (function/app 'left 'state)
                   right-value (function/app 'right 'state)
                   state-mass (function/app 'mass 'state)
                   value-distance (distance left-value right-value)
                   weighted-distance
                   (distance (multiply left-value state-mass)
                             (multiply right-value state-mass))
                   product-distance (multiply value-distance state-mass)
                   product-bound (multiply 'epsilon state-mass)
                   finish-bound (multiply state-mass 'epsilon)
                   scale-bound
                   (function/app
                    (function/const* 'nat/multiply-right-monotone [])
                    state-mass value-distance 'epsilon
                    (function/app 'pointwise 'state))
                   scale-bound
                   (function/app
                    (function/const* 'nat/at-most-rewrite-right [])
                    product-distance product-bound finish-bound
                    (function/app
                     (function/const* 'nat/multiply-commutative [])
                     'epsilon state-mass)
                    scale-bound)]
               (function/app
                (function/const* 'nat/at-most-rewrite-left [])
                weighted-distance product-distance finish-bound
                (function/app
                 (function/const* 'nat/distance-multiply-right [])
                 left-value right-value state-mass)
                scale-bound)))
            sum-bound
            (function/app
             (function/const* 'list/nat-map-sum-distance-bound-by [U])
             'A left-weighted right-weighted bound-weighted
             weighted-pointwise source-list)
            sum-equality
            (function/app
             (function/const* 'list/nat-map-sum-multiply-right [U])
             'A 'mass 'epsilon source-list)]
        (function/app
         (function/const* 'nat/at-most-rewrite-right [])
         (distance (expectation 'A 'source 'mass 'left)
                   (expectation 'A 'source 'mass 'right))
         bound-sum finish sum-equality sum-bound)))}))

(def theorem-specs
  [multiply-successor-right-spec multiply-commutative-spec
   distance-multiply-right-spec distance-multiply-left-spec
   at-most-rewrite-right-spec list-map-sum-distance-bound-spec
   at-most-rewrite-left-spec list-map-sum-distance-bound-by-spec
   list-map-sum-multiply-right-spec expectation-distance-bound-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat contraction expression failed elaboration"
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
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-metric-contraction}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat contraction theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
