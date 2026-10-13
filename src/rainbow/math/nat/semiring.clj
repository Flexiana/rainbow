(ns rainbow.math.nat.semiring
  "Constructive natural semiring laws needed by rational proof data."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat value))

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

(def add-left-cancel-spec
  (let [motive
        (function/lam
         [['prefix nat]]
         (function/forall
          [['left nat] ['right nat]
           ['same (equality (add 'prefix 'left)
                            (add 'prefix 'right))]]
          (equality 'left 'right)))]
    {:name 'nat/add-left-cancel
     :universes []
     :type
     (function/forall
      [['prefix nat] ['left nat] ['right nat]
       ['same (equality (add 'prefix 'left) (add 'prefix 'right))]]
      (equality 'left 'right))
     :value
     (function/lam
      [['prefix nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['left nat] ['right nat] ['same (equality 'left 'right)]]
        'same)
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['left nat] ['right nat]
         ['same
          (equality (succ (add 'previous 'left))
                    (succ (add 'previous 'right)))]]
        (function/app
         'induction-hypothesis 'left 'right
         (function/app (function/const* 'nat/successor-injective [])
                       (add 'previous 'left) (add 'previous 'right)
                       'same)))
       'prefix))}))

(def multiply-one-right-spec
  (let [motive
        (function/lam
         [['value nat]]
         (equality (multiply 'value one) 'value))]
    {:name 'nat/multiply-one-right
     :universes []
     :type
     (function/forall
      [['value nat]] (equality (multiply 'value one) 'value))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (reflexive zero)
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (congruent
         (function/lam [['candidate nat]] (succ 'candidate))
         (multiply 'previous one) 'previous 'induction-hypothesis))
       'value))}))

(def multiply-associative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['middle nat] ['right nat]]
          (equality
           (multiply (multiply 'left 'middle) 'right)
           (multiply 'left (multiply 'middle 'right)))))]
    {:name 'nat/multiply-associative
     :universes []
     :type
     (function/forall
      [['left nat] ['middle nat] ['right nat]]
      (equality
       (multiply (multiply 'left 'middle) 'right)
       (multiply 'left (multiply 'middle 'right))))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam [['middle nat] ['right nat]] (reflexive zero))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['middle nat] ['right nat]]
        (let [previous-product (multiply 'previous 'middle)
              middle-right (multiply 'middle 'right)
              start (multiply (add 'middle previous-product) 'right)
              expanded
              (add middle-right (multiply previous-product 'right))
              finish
              (add middle-right (multiply 'previous middle-right))
              distribute
              (function/app (function/const* 'nat/multiply-add-left [])
                            'middle previous-product 'right)
              replace-tail
              (congruent
               (function/lam
                [['candidate nat]] (add middle-right 'candidate))
               (multiply previous-product 'right)
               (multiply 'previous middle-right)
               (function/app 'induction-hypothesis 'middle 'right))]
          (transitive start expanded finish distribute replace-tail)))
       'left))}))

(def multiply-swap-right-spec
  {:name 'nat/multiply-swap-right
   :universes []
   :type
   (function/forall
    [['left nat] ['middle nat] ['right nat]]
    (equality
     (multiply (multiply 'left 'middle) 'right)
     (multiply (multiply 'left 'right) 'middle)))
   :value
   (function/lam
    [['left nat] ['middle nat] ['right nat]]
    (let [start (multiply (multiply 'left 'middle) 'right)
          associated (multiply 'left (multiply 'middle 'right))
          swapped (multiply 'left (multiply 'right 'middle))
          finish (multiply (multiply 'left 'right) 'middle)
          associate
          (function/app (function/const* 'nat/multiply-associative [])
                        'left 'middle 'right)
          commute
          (congruent
           (function/lam [['value nat]] (multiply 'left 'value))
           (multiply 'middle 'right) (multiply 'right 'middle)
           (function/app (function/const* 'nat/multiply-commutative [])
                         'middle 'right))
          unassociate
          (symmetric
           finish swapped
           (function/app (function/const* 'nat/multiply-associative [])
                         'left 'right 'middle))]
      (transitive
       start associated finish
       associate
       (transitive associated swapped finish commute unassociate))))})

(def multiply-four-reorder-spec
  {:name 'nat/multiply-four-reorder
   :universes []
   :type
   (function/forall
    [['first nat] ['second nat] ['third nat] ['fourth nat]]
    (equality
     (multiply (multiply 'first 'second)
               (multiply 'third 'fourth))
     (multiply (multiply 'first 'third)
               (multiply 'second 'fourth))))
   :value
   (function/lam
    [['first nat] ['second nat] ['third nat] ['fourth nat]]
    (let [start
          (multiply (multiply 'first 'second)
                    (multiply 'third 'fourth))
          first-associated
          (multiply 'first
                    (multiply 'second (multiply 'third 'fourth)))
          second-associated
          (multiply 'first
                    (multiply (multiply 'second 'third) 'fourth))
          swapped
          (multiply 'first
                    (multiply (multiply 'third 'second) 'fourth))
          third-associated
          (multiply 'first
                    (multiply 'third (multiply 'second 'fourth)))
          finish
          (multiply (multiply 'first 'third)
                    (multiply 'second 'fourth))
          associate-first
          (function/app (function/const* 'nat/multiply-associative [])
                        'first 'second (multiply 'third 'fourth))
          unassociate-middle
          (congruent
           (function/lam [['value nat]] (multiply 'first 'value))
           (multiply 'second (multiply 'third 'fourth))
           (multiply (multiply 'second 'third) 'fourth)
           (symmetric
            (multiply (multiply 'second 'third) 'fourth)
            (multiply 'second (multiply 'third 'fourth))
            (function/app
             (function/const* 'nat/multiply-associative [])
             'second 'third 'fourth)))
          commute-middle
          (congruent
           (function/lam
            [['value nat]]
            (multiply 'first (multiply 'value 'fourth)))
           (multiply 'second 'third) (multiply 'third 'second)
           (function/app (function/const* 'nat/multiply-commutative [])
                         'second 'third))
          associate-middle
          (congruent
           (function/lam [['value nat]] (multiply 'first 'value))
           (multiply (multiply 'third 'second) 'fourth)
           (multiply 'third (multiply 'second 'fourth))
           (function/app
            (function/const* 'nat/multiply-associative [])
            'third 'second 'fourth))
          unassociate-first
          (symmetric
           finish third-associated
           (function/app
            (function/const* 'nat/multiply-associative [])
            'first 'third (multiply 'second 'fourth)))
          first-two
          (transitive start first-associated second-associated
                      associate-first unassociate-middle)
          first-three
          (transitive start second-associated swapped
                      first-two commute-middle)
          first-four
          (transitive start swapped third-associated
                      first-three associate-middle)]
      (transitive start third-associated finish
                  first-four unassociate-first)))})

(def multiply-successor-right-cancel-spec
  (let [cancel-type
        (fn [left]
          (function/forall
           [['right nat] ['factor nat]
            ['same
             (equality (multiply left (succ 'factor))
                       (multiply 'right (succ 'factor)))]]
           (equality left 'right)))
        motive (function/lam [['left nat]] (cancel-type 'left))]
    {:name 'nat/multiply-successor-right-cancel
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['factor nat]
       ['same
        (equality (multiply 'left (succ 'factor))
                  (multiply 'right (succ 'factor)))]]
      (equality 'left 'right))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam [['candidate nat]]
                       (function/forall
                        [['factor nat]
                         ['same
                          (equality
                           zero
                           (multiply 'candidate (succ 'factor)))]]
                        (equality zero 'candidate)))
         (function/lam [['factor nat] ['ignored (equality zero zero)]]
                       (reflexive zero))
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['factor nat]
              ['same
               (equality
                zero
                (multiply 'right-previous (succ 'factor)))]]
             (equality zero 'right-previous))]
           ['factor nat]
           ['same
            (equality
             zero
             (succ (add 'factor
                        (multiply 'right-previous (succ 'factor)))))] ]
          (function/app
           (function/const* 'proposition/explode [])
           (equality zero (succ 'right-previous))
           (function/app
            (function/const* 'nat/zero-not-successor [])
            (add 'factor (multiply 'right-previous (succ 'factor)))
            'same)))
         'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (cancel-type 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/forall
           [['factor nat]
            ['same
             (equality
              (multiply (succ 'left-previous) (succ 'factor))
              (multiply 'candidate (succ 'factor)))]]
           (equality (succ 'left-previous) 'candidate)))
         (function/lam
          [['factor nat]
           ['same
            (equality
             (succ (add 'factor
                        (multiply 'left-previous (succ 'factor))))
             zero)]]
          (function/app
           (function/const* 'proposition/explode [])
           (equality (succ 'left-previous) zero)
           (function/app
            (function/const* 'nat/zero-not-successor [])
            (add 'factor (multiply 'left-previous (succ 'factor)))
            (symmetric
             (succ (add 'factor
                        (multiply 'left-previous (succ 'factor))))
             zero 'same))))
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['factor nat]
              ['same
               (equality
                (multiply (succ 'left-previous) (succ 'factor))
                (multiply 'right-previous (succ 'factor)))]]
             (equality (succ 'left-previous) 'right-previous))]
           ['factor nat]
           ['same
            (equality
             (succ (add 'factor
                        (multiply 'left-previous (succ 'factor))))
             (succ (add 'factor
                        (multiply 'right-previous (succ 'factor)))))] ]
          (let [same-sums
                (function/app
                 (function/const* 'nat/successor-injective [])
                 (add 'factor
                      (multiply 'left-previous (succ 'factor)))
                 (add 'factor
                      (multiply 'right-previous (succ 'factor)))
                 'same)
                same-products
                (function/app
                 (function/const* 'nat/add-left-cancel [])
                 'factor
                 (multiply 'left-previous (succ 'factor))
                 (multiply 'right-previous (succ 'factor))
                 same-sums)
                same-previous
                (function/app 'induction-hypothesis
                              'right-previous 'factor same-products)]
            (congruent
             (function/lam [['candidate nat]] (succ 'candidate))
             'left-previous 'right-previous same-previous)))
         'right))
       'left))}))

(def theorem-specs
  [add-left-cancel-spec multiply-one-right-spec
   multiply-associative-spec multiply-swap-right-spec
   multiply-four-reorder-spec multiply-successor-right-cancel-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat semiring expression failed elaboration"
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
          {:origin :native :producer :nonnegative-rational-foundation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat semiring theorem was rejected"
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
