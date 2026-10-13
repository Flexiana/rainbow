(ns rainbow.math.nat.linear-order
  "Executable decision data, min/max, and three-way comparison for Nat."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def sort-u [:sort U])
(def type-u [:sort [:succ U]])
(def decidable-equality-level [:imax U [:max type-level U]])
(def decidable-equality-sort [:sort decidable-equality-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(def ordering-spec
  {:block/schema-version 1
   :block/alias 'order/Ordering
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'order/less :constructor/fields []}
    {:constructor/alias 'order/equal :constructor/fields []}
    {:constructor/alias 'order/greater :constructor/fields []}]})

(defn- succ [value]
  (function/app successor value))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- strict-below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- decide-at-most [left right]
  (function/app (function/const* 'nat/decide-at-most []) left right))

(defn- decide-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

(defn- if-data [level carrier proposition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [level])
                carrier proposition decision then-value else-value))

(def decidable-relation-spec
  {:name 'logic/decidable-relation
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['relation (function/arrow 'A 'A 'Prop)]]
    type-u)
   :value
   (function/lam
    [['A type-u] ['ignored (function/arrow 'A 'A 'Prop)]]
    (function/arrow 'A 'A bool))})

(def decidable-equality-spec
  {:name 'logic/decidable-equality
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall [['A sort-u]] decidable-equality-sort)
   :value
   (function/lam [['A sort-u]] (function/arrow 'A 'A bool))})

(def if-data-spec
  {:name 'logic/if-data
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A sort-u] ['condition 'Prop] ['decision bool]]
    (function/arrow 'A 'A 'A))
   :value
   (function/lam
    [['A sort-u] ['ignored-condition 'Prop] ['decision bool]
     ['then-value 'A] ['else-value 'A]]
    (function/app
     (function/const* 'data/Bool.rec [U])
     (function/lam [['ignored bool]] 'A)
     'else-value 'then-value 'decision))})

(def min-operation-spec
  {:name 'order/min-operation
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['dictionary (function/arrow 'A 'A 'A)]]
    (function/arrow 'A 'A 'A))
   :value
   (function/lam
    [['A type-u] ['dictionary (function/arrow 'A 'A 'A)]]
    'dictionary)})

(def max-operation-spec
  {:name 'order/max-operation
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type (:type min-operation-spec)
   :value (:value min-operation-spec)})

(def le-class-spec
  {:name 'order/le-class
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['relation (function/arrow 'A 'A 'Prop)]]
    (function/arrow 'A 'A 'Prop))
   :value
   (function/lam
    [['A type-u] ['relation (function/arrow 'A 'A 'Prop)]]
    'relation)})

(def lt-class-spec
  {:name 'order/lt-class
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type (:type le-class-spec)
   :value (:value le-class-spec)})

(def nat-decide-at-most-spec
  {:name 'nat/decide-at-most
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat bool)
   :value
   (function/lam
    [['left nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] (function/arrow nat bool))
     (function/lam [['right nat]] true-value)
     (function/lam
      [['left-previous nat]
       ['previous-decision (function/arrow nat bool)]]
      (function/lam
       [['right nat]]
       (function/app
        (function/const* 'data/Nat.rec [type-level])
        (function/lam [['ignored nat]] bool)
        false-value
        (function/lam
         [['right-previous nat] ['ignored bool]]
         (function/app 'previous-decision 'right-previous))
        'right)))
     'left))})

(def nat-decide-strict-below-spec
  {:name 'nat/decide-strict-below
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat bool)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (decide-at-most (succ 'left) 'right))})

(def nat-decide-equality-spec
  {:name 'nat/decide-equality
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat bool)
   :value
   (function/lam
    [['left nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] (function/arrow nat bool))
     (function/lam
      [['right nat]]
      (function/app
       (function/const* 'data/Nat.rec [type-level])
       (function/lam [['ignored nat]] bool)
       true-value
       (function/lam [['right-previous nat] ['ignored bool]] false-value)
       'right))
     (function/lam
      [['left-previous nat]
       ['previous-decision (function/arrow nat bool)]]
      (function/lam
       [['right nat]]
       (function/app
        (function/const* 'data/Nat.rec [type-level])
        (function/lam [['ignored nat]] bool)
        false-value
        (function/lam
         [['right-previous nat] ['ignored bool]]
         (function/app 'previous-decision 'right-previous))
        'right)))
     'left))})

(def nat-min-spec
  {:name 'nat/min
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (if-data type-level nat (at-most 'left 'right)
             (decide-at-most 'left 'right)
             'left 'right))})

(def nat-max-spec
  {:name 'nat/max
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (if-data type-level nat (at-most 'left 'right)
             (decide-at-most 'left 'right)
             'right 'left))})

(def compare-operation-spec
  {:name 'order/compare-operation
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]
     ['dictionary
      (function/arrow 'A 'A (function/const* 'order/Ordering []))]]
    (function/arrow 'A 'A (function/const* 'order/Ordering [])))
   :value
   (function/lam
    [['A type-u]
     ['dictionary
      (function/arrow 'A 'A (function/const* 'order/Ordering []))]]
    'dictionary)})

(def compare-from-less-equal-spec
  {:name 'order/compare-from-less-equal
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['left 'A] ['right 'A]
     ['less-than (function/arrow 'A 'A 'Prop)]
     ['less-decision bool]
     ['equality-decision (function/arrow 'A 'A bool)]]
    (function/const* 'order/Ordering []))
   :value
   (function/lam
    [['A type-u] ['left 'A] ['right 'A]
     ['ignored-less-than (function/arrow 'A 'A 'Prop)]
     ['less-decision bool]
     ['equality-decision (function/arrow 'A 'A bool)]]
    (if-data
     type-level
     (function/const* 'order/Ordering [])
     (function/app 'ignored-less-than 'left 'right)
     'less-decision
     (function/const* 'order/less [])
     (if-data
      type-level
      (function/const* 'order/Ordering [])
      (function/equality [:succ U] 'A 'left 'right)
      (function/app 'equality-decision 'left 'right)
      (function/const* 'order/equal [])
      (function/const* 'order/greater []))))})

(def nat-ordering-spec
  {:name 'nat/ordering
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat (function/const* 'order/Ordering []))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (function/app
     (function/const* 'order/compare-from-less-equal [zero-level])
     nat 'left 'right (function/const* 'nat/strict-below [])
     (function/app (function/const* 'nat/decide-strict-below [])
                   'left 'right)
     (function/const* 'nat/decide-equality [])))})

(def definition-specs
  [decidable-relation-spec decidable-equality-spec if-data-spec
   min-operation-spec max-operation-spec le-class-spec lt-class-spec
   nat-decide-at-most-spec nat-decide-strict-below-spec
   nat-decide-equality-spec nat-min-spec nat-max-spec
   compare-operation-spec compare-from-less-equal-spec nat-ordering-spec])

(def constant-aliases
  {"Min.min" 'order/min-operation
   "Max.max" 'order/max-operation
   "instMinNat" 'nat/min
   "Nat.instMax" 'nat/max
   "ite" 'logic/if-data
   "Nat.le" 'nat/at-most
   "DecidableLE" 'logic/decidable-relation
   "LE.mk" 'order/le-class
   "Nat.decLe" 'nat/decide-at-most
   "inferInstance" 'function/identity
   "Ordering" 'order/Ordering
   "Ord.compare" 'order/compare-operation
   "instOrdNat" 'nat/ordering
   "compareOfLessAndEq" 'order/compare-from-less-equal
   "LT.mk" 'order/lt-class
   "Nat.lt" 'nat/strict-below
   "DecidableLT" 'logic/decidable-relation
   "Nat.decLt" 'nat/decide-strict-below
   "DecidableEq" 'logic/decidable-equality
   "instDecidableEqNat" 'nat/decide-equality})

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat linear-order expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :definition
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :reducible
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :computational-nat-linear-order}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat linear-order definition was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (let [block (environment/resolve-id checked-environment 'order/Ordering)
        installed
        (every? #(environment/resolve-id checked-environment (:name %))
                definition-specs)]
    (cond
      (and block installed) checked-environment

      (or block installed)
      (throw (ex-info "Nat linear-order package is only partially installed"
                      {:ordering-block? (boolean block)
                       :definitions-complete? installed}))

      :else
      (let [added (kernel/add-inductive-block checked-environment ordering-spec)]
        (when-not (= :accepted (:status added))
          (throw (ex-info "Ordering inductive block was rejected"
                          {:result added})))
        (reduce add-spec (:environment added) definition-specs)))))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn block-id [checked-environment]
  (environment/resolve-id checked-environment 'order/Ordering))
