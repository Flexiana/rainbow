(ns rainbow.math.nonnegative-rational
  "Nonnegative rationals as proof data: numerator plus denominator predecessor.

  The representation makes a zero denominator unrepresentable.  Equality is
  deliberately cross-multiplication equivalence rather than product equality;
  no quotient rule or normalization axiom is added to the kernel."
  (:refer-clojure :exclude [denominator numerator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def two (function/app successor one))
(def three (function/app successor two))

(def raw-nonnegative-rational
  (function/app
   (function/const* 'data/Product [type-level type-level]) nat nat))

(def nonnegative-rational
  (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value]
  (function/app successor value))

(defn- add-nat [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- pair [numerator denominator-predecessor]
  (function/app
   (function/const* 'data/pair [type-level type-level])
   nat nat numerator denominator-predecessor))

(defn- numerator [value]
  (function/app
   (function/const* 'nnrat/numerator []) value))

(defn- denominator-predecessor [value]
  (function/app
   (function/const* 'nnrat/denominator-predecessor []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- denominator-combine [left right]
  (function/app
   (function/const* 'nnrat/combine-denominator-predecessors []) left right))

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

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(def carrier-spec
  {:name 'nnrat/NonnegativeRational
   :kind :definition
   :universes []
   :type [:sort type-level]
   :value raw-nonnegative-rational})

(def make-spec
  {:name 'nnrat/make
   :kind :definition
   :universes []
   :type (function/arrow nat nat nonnegative-rational)
   :value
   (function/lam
    [['numerator nat] ['denominator-predecessor nat]]
    (pair 'numerator 'denominator-predecessor))})

(def numerator-spec
  {:name 'nnrat/numerator
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational nat)
   :value
   (function/lam
    [['value nonnegative-rational]]
    (function/app
     (function/const* 'product/first [type-level type-level])
     nat nat 'value))})

(def denominator-predecessor-spec
  {:name 'nnrat/denominator-predecessor
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational nat)
   :value
   (function/lam
    [['value nonnegative-rational]]
    (function/app
     (function/const* 'product/second [type-level type-level])
     nat nat 'value))})

(def denominator-spec
  {:name 'nnrat/denominator
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational nat)
   :value
   (function/lam
    [['value nonnegative-rational]]
    (succ (denominator-predecessor 'value)))})

(def denominator-combine-spec
  {:name 'nnrat/combine-denominator-predecessors
   :kind :definition
   :universes []
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (function/app
     (function/const* 'nat/predecessor [])
     (multiply-nat (succ 'left) (succ 'right))))})

(def zero-spec
  {:name 'nnrat/zero
   :kind :definition
   :universes []
   :type nonnegative-rational
   :value (pair zero zero)})

(def one-spec
  {:name 'nnrat/one
   :kind :definition
   :universes []
   :type nonnegative-rational
   :value (pair one zero)})

(def half-spec
  {:name 'nnrat/half
   :kind :definition
   :universes []
   :type nonnegative-rational
   :value (pair one one)})

(def quarter-spec
  {:name 'nnrat/quarter
   :kind :definition
   :universes []
   :type nonnegative-rational
   :value (pair one three)})

(def equivalent-spec
  {:name 'nnrat/equivalent
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational
                         nonnegative-rational 'Prop)
   :value
   (function/lam
    [['left nonnegative-rational]
     ['right nonnegative-rational]]
    (equality
     (multiply-nat (numerator 'left) (denominator 'right))
     (multiply-nat (numerator 'right) (denominator 'left))))})

(def add-specification
  {:name 'nnrat/add
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational
                         nonnegative-rational nonnegative-rational)
   :value
   (function/lam
    [['left nonnegative-rational]
     ['right nonnegative-rational]]
    (pair
     (add-nat
      (multiply-nat (numerator 'left) (denominator 'right))
      (multiply-nat (numerator 'right) (denominator 'left)))
     (denominator-combine
      (denominator-predecessor 'left)
      (denominator-predecessor 'right))))})

(def multiply-specification
  {:name 'nnrat/multiply
   :kind :definition
   :universes []
   :type (function/arrow nonnegative-rational
                         nonnegative-rational nonnegative-rational)
   :value
   (function/lam
    [['left nonnegative-rational]
     ['right nonnegative-rational]]
    (pair
     (multiply-nat (numerator 'left) (numerator 'right))
     (denominator-combine
      (denominator-predecessor 'left)
      (denominator-predecessor 'right))))})

(def definition-specs
  [carrier-spec make-spec numerator-spec denominator-predecessor-spec denominator-spec
   denominator-combine-spec zero-spec one-spec half-spec quarter-spec
   equivalent-spec add-specification multiply-specification])

(def denominator-combine-law-spec
  {:name 'nnrat/denominator-combine
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]]
    (equality
     (succ (denominator-combine 'left 'right))
     (multiply-nat (succ 'left) (succ 'right))))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (function/app
     (function/const* 'equality/reflexive [type-level])
     nat
     (multiply-nat (succ 'left) (succ 'right))))})

(def equivalent-reflexive-spec
  {:name 'nnrat/equivalent-reflexive
   :universes []
   :type
   (function/forall
    [['value nonnegative-rational]] (equivalent 'value 'value))
   :value
   (function/lam
    [['value nonnegative-rational]]
    (function/app
     (function/const* 'equality/reflexive [type-level])
     nat
     (multiply-nat (numerator 'value) (denominator 'value))))})

(def equivalent-symmetric-spec
  {:name 'nnrat/equivalent-symmetric
   :universes []
   :type
   (function/forall
    [['left nonnegative-rational]
     ['right nonnegative-rational]
     ['same (equivalent 'left 'right)]]
    (equivalent 'right 'left))
   :value
   (function/lam
    [['left nonnegative-rational]
     ['right nonnegative-rational]
     ['same (equivalent 'left 'right)]]
    (function/app
     (function/const* 'equality/symmetric [type-level])
     nat
     (multiply-nat (numerator 'left) (denominator 'right))
     (multiply-nat (numerator 'right) (denominator 'left))
     'same))})

(def equivalent-transitive-spec
  {:name 'nnrat/equivalent-transitive
   :universes []
   :type
   (function/forall
    [['left nonnegative-rational]
     ['middle nonnegative-rational]
     ['right nonnegative-rational]
     ['left-middle (equivalent 'left 'middle)]
     ['middle-right (equivalent 'middle 'right)]]
    (equivalent 'left 'right))
   :value
   (function/lam
    [['left nonnegative-rational]
     ['middle nonnegative-rational]
     ['right nonnegative-rational]
     ['left-middle (equivalent 'left 'middle)]
     ['middle-right (equivalent 'middle 'right)]]
    (let [left-numerator (numerator 'left)
          left-denominator (denominator 'left)
          middle-numerator (numerator 'middle)
          middle-denominator (denominator 'middle)
          right-numerator (numerator 'right)
          right-denominator (denominator 'right)
          start
          (multiply-nat
           (multiply-nat left-numerator right-denominator)
           middle-denominator)
          after-first-swap
          (multiply-nat
           (multiply-nat left-numerator middle-denominator)
           right-denominator)
          after-left-equivalence
          (multiply-nat
           (multiply-nat middle-numerator left-denominator)
           right-denominator)
          after-second-swap
          (multiply-nat
           (multiply-nat middle-numerator right-denominator)
           left-denominator)
          after-right-equivalence
          (multiply-nat
           (multiply-nat right-numerator middle-denominator)
           left-denominator)
          finish
          (multiply-nat
           (multiply-nat right-numerator left-denominator)
           middle-denominator)
          swap-first
          (function/app
           (function/const* 'nat/multiply-swap-right [])
           left-numerator right-denominator middle-denominator)
          replace-left
          (congruent
           (function/lam
            [['value nat]] (multiply-nat 'value right-denominator))
           (multiply-nat left-numerator middle-denominator)
           (multiply-nat middle-numerator left-denominator)
           'left-middle)
          swap-second
          (function/app
           (function/const* 'nat/multiply-swap-right [])
           middle-numerator left-denominator right-denominator)
          replace-right
          (congruent
           (function/lam
            [['value nat]] (multiply-nat 'value left-denominator))
           (multiply-nat middle-numerator right-denominator)
           (multiply-nat right-numerator middle-denominator)
           'middle-right)
          swap-third
          (function/app
           (function/const* 'nat/multiply-swap-right [])
           right-numerator middle-denominator left-denominator)
          first-two
          (transitive start after-first-swap after-left-equivalence
                      swap-first replace-left)
          first-three
          (transitive start after-left-equivalence after-second-swap
                      first-two swap-second)
          first-four
          (transitive start after-second-swap after-right-equivalence
                      first-three replace-right)
          common-factor-equality
          (transitive start after-right-equivalence finish
                      first-four swap-third)]
      (function/app
       (function/const* 'nat/multiply-successor-right-cancel [])
       (multiply-nat left-numerator right-denominator)
       (multiply-nat right-numerator left-denominator)
       (denominator-predecessor 'middle)
       common-factor-equality)))})

(def multiply-respects-equivalence-spec
  {:name 'nnrat/multiply-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left nonnegative-rational]
     ['left-equivalent nonnegative-rational]
     ['right nonnegative-rational]
     ['right-equivalent nonnegative-rational]
     ['same-left (equivalent 'left 'left-equivalent)]
     ['same-right (equivalent 'right 'right-equivalent)]]
    (equivalent
     (function/app (function/const* 'nnrat/multiply [])
                   'left 'right)
     (function/app (function/const* 'nnrat/multiply [])
                   'left-equivalent 'right-equivalent)))
   :value
   (function/lam
    [['left nonnegative-rational]
     ['left-equivalent nonnegative-rational]
     ['right nonnegative-rational]
     ['right-equivalent nonnegative-rational]
     ['same-left (equivalent 'left 'left-equivalent)]
     ['same-right (equivalent 'right 'right-equivalent)]]
    (let [left-numerator (numerator 'left)
          left-denominator (denominator 'left)
          equivalent-left-numerator (numerator 'left-equivalent)
          equivalent-left-denominator (denominator 'left-equivalent)
          right-numerator (numerator 'right)
          right-denominator (denominator 'right)
          equivalent-right-numerator (numerator 'right-equivalent)
          equivalent-right-denominator (denominator 'right-equivalent)
          start
          (multiply-nat
           (multiply-nat left-numerator right-numerator)
           (multiply-nat equivalent-left-denominator
                         equivalent-right-denominator))
          paired-equivalences
          (multiply-nat
           (multiply-nat left-numerator equivalent-left-denominator)
           (multiply-nat right-numerator equivalent-right-denominator))
          after-left
          (multiply-nat
           (multiply-nat equivalent-left-numerator left-denominator)
           (multiply-nat right-numerator equivalent-right-denominator))
          after-right
          (multiply-nat
           (multiply-nat equivalent-left-numerator left-denominator)
           (multiply-nat equivalent-right-numerator right-denominator))
          finish
          (multiply-nat
           (multiply-nat equivalent-left-numerator
                         equivalent-right-numerator)
           (multiply-nat left-denominator right-denominator))
          group-equivalences
          (function/app
           (function/const* 'nat/multiply-four-reorder [])
           left-numerator right-numerator
           equivalent-left-denominator equivalent-right-denominator)
          replace-left
          (congruent
           (function/lam
            [['value nat]]
            (multiply-nat
             'value
             (multiply-nat right-numerator
                           equivalent-right-denominator)))
           (multiply-nat left-numerator equivalent-left-denominator)
           (multiply-nat equivalent-left-numerator left-denominator)
           'same-left)
          replace-right
          (congruent
           (function/lam
            [['value nat]]
            (multiply-nat
             (multiply-nat equivalent-left-numerator left-denominator)
             'value))
           (multiply-nat right-numerator equivalent-right-denominator)
           (multiply-nat equivalent-right-numerator right-denominator)
           'same-right)
          ungroup-result
          (function/app
           (function/const* 'nat/multiply-four-reorder [])
           equivalent-left-numerator left-denominator
           equivalent-right-numerator right-denominator)
          first-two
          (transitive start paired-equivalences after-left
                      group-equivalences replace-left)
          first-three
          (transitive start after-left after-right
                      first-two replace-right)]
      (transitive start after-right finish
                  first-three ungroup-result)))})

(def add-respects-equivalence-spec
  {:name 'nnrat/add-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left nonnegative-rational]
     ['left-equivalent nonnegative-rational]
     ['right nonnegative-rational]
     ['right-equivalent nonnegative-rational]
     ['same-left (equivalent 'left 'left-equivalent)]
     ['same-right (equivalent 'right 'right-equivalent)]]
    (equivalent
     (function/app (function/const* 'nnrat/add []) 'left 'right)
     (function/app (function/const* 'nnrat/add [])
                   'left-equivalent 'right-equivalent)))
   :value
   (function/lam
    [['left nonnegative-rational]
     ['left-equivalent nonnegative-rational]
     ['right nonnegative-rational]
     ['right-equivalent nonnegative-rational]
     ['same-left (equivalent 'left 'left-equivalent)]
     ['same-right (equivalent 'right 'right-equivalent)]]
    (let [a (numerator 'left)
          b (denominator 'left)
          c (numerator 'left-equivalent)
          d (denominator 'left-equivalent)
          e (numerator 'right)
          f (denominator 'right)
          g (numerator 'right-equivalent)
          h (denominator 'right-equivalent)
          left-first (multiply-nat a f)
          left-second (multiply-nat e b)
          right-first (multiply-nat c h)
          right-second (multiply-nat g d)
          left-factor (multiply-nat d h)
          right-factor (multiply-nat b f)
          first-start (multiply-nat left-first left-factor)
          first-grouped
          (multiply-nat (multiply-nat a d) (multiply-nat f h))
          first-commuted
          (multiply-nat (multiply-nat a d) (multiply-nat h f))
          first-replaced
          (multiply-nat (multiply-nat c b) (multiply-nat h f))
          first-finish (multiply-nat right-first right-factor)
          first-group
          (function/app (function/const* 'nat/multiply-four-reorder [])
                        a f d h)
          first-commute
          (congruent
           (function/lam
            [['value nat]] (multiply-nat (multiply-nat a d) 'value))
           (multiply-nat f h) (multiply-nat h f)
           (function/app (function/const* 'nat/multiply-commutative [])
                         f h))
          first-replace
          (congruent
           (function/lam
            [['value nat]] (multiply-nat 'value (multiply-nat h f)))
           (multiply-nat a d) (multiply-nat c b) 'same-left)
          first-ungroup
          (function/app (function/const* 'nat/multiply-four-reorder [])
                        c b h f)
          first-chain-two
          (transitive first-start first-grouped first-commuted
                      first-group first-commute)
          first-chain-three
          (transitive first-start first-commuted first-replaced
                      first-chain-two first-replace)
          first-proof
          (transitive first-start first-replaced first-finish
                      first-chain-three first-ungroup)
          second-start (multiply-nat left-second left-factor)
          second-commuted-factor
          (multiply-nat (multiply-nat e b) (multiply-nat h d))
          second-grouped
          (multiply-nat (multiply-nat e h) (multiply-nat b d))
          second-replaced
          (multiply-nat (multiply-nat g f) (multiply-nat b d))
          second-commuted-middle
          (multiply-nat (multiply-nat g f) (multiply-nat d b))
          second-ungrouped
          (multiply-nat (multiply-nat g d) (multiply-nat f b))
          second-finish (multiply-nat right-second right-factor)
          second-commute-factor
          (congruent
           (function/lam
            [['value nat]] (multiply-nat (multiply-nat e b) 'value))
           (multiply-nat d h) (multiply-nat h d)
           (function/app (function/const* 'nat/multiply-commutative [])
                         d h))
          second-group
          (function/app (function/const* 'nat/multiply-four-reorder [])
                        e b h d)
          second-replace
          (congruent
           (function/lam
            [['value nat]] (multiply-nat 'value (multiply-nat b d)))
           (multiply-nat e h) (multiply-nat g f) 'same-right)
          second-commute-middle
          (congruent
           (function/lam
            [['value nat]] (multiply-nat (multiply-nat g f) 'value))
           (multiply-nat b d) (multiply-nat d b)
           (function/app (function/const* 'nat/multiply-commutative [])
                         b d))
          second-ungroup
          (function/app (function/const* 'nat/multiply-four-reorder [])
                        g f d b)
          second-commute-finish
          (congruent
           (function/lam
            [['value nat]] (multiply-nat (multiply-nat g d) 'value))
           (multiply-nat f b) (multiply-nat b f)
           (function/app (function/const* 'nat/multiply-commutative [])
                         f b))
          second-chain-two
          (transitive second-start second-commuted-factor second-grouped
                      second-commute-factor second-group)
          second-chain-three
          (transitive second-start second-grouped second-replaced
                      second-chain-two second-replace)
          second-chain-four
          (transitive second-start second-replaced second-commuted-middle
                      second-chain-three second-commute-middle)
          second-chain-five
          (transitive second-start second-commuted-middle second-ungrouped
                      second-chain-four second-ungroup)
          second-proof
          (transitive second-start second-ungrouped second-finish
                      second-chain-five second-commute-finish)
          start
          (multiply-nat (add-nat left-first left-second) left-factor)
          distributed
          (add-nat first-start second-start)
          replaced-first
          (add-nat first-finish second-start)
          replaced-both
          (add-nat first-finish second-finish)
          finish
          (multiply-nat (add-nat right-first right-second) right-factor)
          distribute-left
          (function/app (function/const* 'nat/multiply-add-left [])
                        left-first left-second left-factor)
          replace-first
          (congruent
           (function/lam [['value nat]] (add-nat 'value second-start))
           first-start first-finish first-proof)
          replace-second
          (congruent
           (function/lam [['value nat]] (add-nat first-finish 'value))
           second-start second-finish second-proof)
          collect-right
          (symmetric
           finish replaced-both
           (function/app (function/const* 'nat/multiply-add-left [])
                         right-first right-second right-factor))
          outer-first
          (transitive start distributed replaced-first
                      distribute-left replace-first)
          outer-second
          (transitive start replaced-first replaced-both
                      outer-first replace-second)]
      (transitive start replaced-both finish
                  outer-second collect-right)))})

(def theorem-specs
  [denominator-combine-law-spec equivalent-reflexive-spec
   equivalent-symmetric-spec equivalent-transitive-spec
   add-respects-equivalence-spec multiply-respects-equivalence-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nonnegative-rational expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :nonnegative-rational-foundation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nonnegative-rational declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (-> checked-environment extend-definitions extend-theorems))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
