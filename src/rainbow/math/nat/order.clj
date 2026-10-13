(ns rainbow.math.nat.order
  "Constructive monotonicity for Nat arithmetic and finite expectation."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nat-map-sum [U])
                element mapping source))

(defn- expectation [element source mass value]
  (function/app
   (function/const* 'probability/expectation-numerator [U])
   element source mass value))

(defn- witness [value evidence]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['extra nat]]
                 (equality (add 'left 'extra) 'right))
   value evidence))

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

(def at-most-reflexive-spec
  {:name 'nat/at-most-reflexive
   :universes []
   :type (function/forall [['value nat]] (at-most 'value 'value))
   :value
   (function/lam
    [['value nat]]
    (function/app
     (function/const* 'proposition/witness [type-level])
     nat
     (function/lam [['extra nat]]
                   (equality (add 'value 'extra) 'value))
     zero
     (function/app
      (function/const* 'algebra/nat-add-zero-right []) 'value)))})

(def at-most-transitive-spec
  {:name 'nat/at-most-transitive
   :universes []
   :type
   (function/forall
    [['left nat] ['middle nat] ['right nat]
     ['first (at-most 'left 'middle)]
     ['second (at-most 'middle 'right)]]
    (at-most 'left 'right))
   :value
   (function/lam
    [['left nat] ['middle nat] ['right nat]
     ['first (at-most 'left 'middle)]
     ['second (at-most 'middle 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat (function/lam [['first-extra nat]]
                       (equality (add 'left 'first-extra) 'middle))
     (at-most 'left 'right) 'first
     (function/lam
      [['first-extra nat]
       ['same-first (equality (add 'left 'first-extra) 'middle)]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat (function/lam [['second-extra nat]]
                         (equality (add 'middle 'second-extra) 'right))
       (at-most 'left 'right) 'second
       (function/lam
        [['second-extra nat]
         ['same-second (equality (add 'middle 'second-extra) 'right)]]
        (let [combined (add 'first-extra 'second-extra)
              start (add 'left combined)
              associated (add (add 'left 'first-extra) 'second-extra)
              replaced (add 'middle 'second-extra)
              reassociate
              (symmetric
               associated start
               (function/app (function/const* 'nat/add-associative [])
                             'left 'first-extra 'second-extra))
              replace-first
              (congruent
               (function/lam [['value nat]] (add 'value 'second-extra))
               (add 'left 'first-extra) 'middle 'same-first)
              complete
              (transitive start associated replaced reassociate replace-first)
              complete (transitive start replaced 'right complete 'same-second)]
          (function/app
           (function/const* 'proposition/witness [type-level])
           nat
           (function/lam [['extra nat]]
                         (equality (add 'left 'extra) 'right))
           combined complete)))))))})

(def at-most-successor-spec
  {:name 'nat/at-most-successor
   :universes []
   :type
   (function/forall
    [['value nat]]
    (at-most 'value (function/app successor 'value)))
   :value
   (function/lam
    [['value nat]]
    (let [start (add 'value one)
          middle (function/app successor (add 'value zero))
          finish (function/app successor 'value)
          add-successor
          (function/app
           (function/const* 'algebra/nat-add-successor-right [])
           'value zero)
          remove-zero
          (congruent
           (function/lam [['candidate nat]]
                         (function/app successor 'candidate))
           (add 'value zero) 'value
           (function/app
            (function/const* 'algebra/nat-add-zero-right []) 'value))]
      (function/app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam [['extra nat]]
                     (equality (add 'value 'extra) finish))
       one
       (transitive start middle finish add-successor remove-zero))))})

(def add-left-monotone-spec
  {:name 'nat/add-left-monotone
   :universes []
   :type
   (function/forall
    [['prefix nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (at-most (add 'prefix 'left) (add 'prefix 'right)))
   :value
   (function/lam
    [['prefix nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat (function/lam [['extra nat]]
                       (equality (add 'left 'extra) 'right))
     (at-most (add 'prefix 'left) (add 'prefix 'right)) 'ordered
     (function/lam
      [['extra nat] ['same (equality (add 'left 'extra) 'right)]]
      (let [start (add (add 'prefix 'left) 'extra)
            middle (add 'prefix (add 'left 'extra))
            finish (add 'prefix 'right)
            associate
            (function/app (function/const* 'nat/add-associative [])
                          'prefix 'left 'extra)
            replace
            (congruent (function/lam [['value nat]] (add 'prefix 'value))
                       (add 'left 'extra) 'right 'same)]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['delta nat]]
                       (equality (add (add 'prefix 'left) 'delta) finish))
         'extra (transitive start middle finish associate replace))))))})

(def add-right-monotone-spec
  {:name 'nat/add-right-monotone
   :universes []
   :type
   (function/forall
    [['suffix nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (at-most (add 'left 'suffix) (add 'right 'suffix)))
   :value
   (function/lam
    [['suffix nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat (function/lam [['extra nat]]
                       (equality (add 'left 'extra) 'right))
     (at-most (add 'left 'suffix) (add 'right 'suffix)) 'ordered
     (function/lam
      [['extra nat] ['same (equality (add 'left 'extra) 'right)]]
      (let [start (add (add 'left 'suffix) 'extra)
            step-one (add 'left (add 'suffix 'extra))
            step-two (add 'left (add 'extra 'suffix))
            step-three (add (add 'left 'extra) 'suffix)
            finish (add 'right 'suffix)
            first
            (function/app (function/const* 'nat/add-associative [])
                          'left 'suffix 'extra)
            swap-inner
            (congruent
             (function/lam [['value nat]] (add 'left 'value))
             (add 'suffix 'extra) (add 'extra 'suffix)
             (function/app (function/const* 'nat/add-commutative [])
                           'suffix 'extra))
            reassociate
            (symmetric
             step-three step-two
             (function/app (function/const* 'nat/add-associative [])
                           'left 'extra 'suffix))
            replace
            (congruent (function/lam [['value nat]] (add 'value 'suffix))
                       (add 'left 'extra) 'right 'same)
            first-two (transitive start step-one step-two first swap-inner)
            first-three
            (transitive start step-two step-three first-two reassociate)]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['delta nat]]
                       (equality (add (add 'left 'suffix) 'delta) finish))
         'extra (transitive start step-three finish first-three replace))))))})

(def add-monotone-spec
  {:name 'nat/add-monotone
   :universes []
   :type
   (function/forall
    [['left-a nat] ['right-a nat] ['left-b nat] ['right-b nat]
     ['ordered-a (at-most 'left-a 'right-a)]
     ['ordered-b (at-most 'left-b 'right-b)]]
    (at-most (add 'left-a 'left-b) (add 'right-a 'right-b)))
   :value
   (function/lam
    [['left-a nat] ['right-a nat] ['left-b nat] ['right-b nat]
     ['ordered-a (at-most 'left-a 'right-a)]
     ['ordered-b (at-most 'left-b 'right-b)]]
    (function/app
     (function/const* 'nat/at-most-transitive [])
     (add 'left-a 'left-b) (add 'right-a 'left-b)
     (add 'right-a 'right-b)
     (function/app (function/const* 'nat/add-right-monotone [])
                   'left-b 'left-a 'right-a 'ordered-a)
     (function/app (function/const* 'nat/add-left-monotone [])
                   'right-a 'left-b 'right-b 'ordered-b)))})

(def multiply-add-left-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat] ['factor nat]]
          (equality (multiply (add 'left 'right) 'factor)
                    (add (multiply 'left 'factor)
                         (multiply 'right 'factor)))))]
    {:name 'nat/multiply-add-left
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['factor nat]]
      (equality (multiply (add 'left 'right) 'factor)
                (add (multiply 'left 'factor)
                     (multiply 'right 'factor))))
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
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['right nat] ['factor nat]]
        (let [left-sum (multiply (add 'previous 'right) 'factor)
              left-product (multiply 'previous 'factor)
              right-product (multiply 'right 'factor)
              start (add 'factor left-sum)
              middle (add 'factor (add left-product right-product))
              finish (add (add 'factor left-product) right-product)
              replace
              (congruent (function/lam [['value nat]] (add 'factor 'value))
                         left-sum (add left-product right-product)
                         (function/app 'induction-hypothesis 'right 'factor))
              reassociate
              (symmetric
               finish middle
               (function/app (function/const* 'nat/add-associative [])
                             'factor left-product right-product))]
          (transitive start middle finish replace reassociate)))
       'left))}))

(def multiply-right-monotone-spec
  {:name 'nat/multiply-right-monotone
   :universes []
   :type
   (function/forall
    [['factor nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (at-most (multiply 'left 'factor) (multiply 'right 'factor)))
   :value
   (function/lam
    [['factor nat] ['left nat] ['right nat]
     ['ordered (at-most 'left 'right)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat (function/lam [['extra nat]]
                       (equality (add 'left 'extra) 'right))
     (at-most (multiply 'left 'factor) (multiply 'right 'factor))
     'ordered
     (function/lam
      [['extra nat] ['same (equality (add 'left 'extra) 'right)]]
      (let [extra-product (multiply 'extra 'factor)
            start (add (multiply 'left 'factor) extra-product)
            combined (multiply (add 'left 'extra) 'factor)
            finish (multiply 'right 'factor)
            distribute
            (symmetric
             combined start
             (function/app (function/const* 'nat/multiply-add-left [])
                           'left 'extra 'factor))
            replace
            (congruent (function/lam [['value nat]] (multiply 'value 'factor))
                       (add 'left 'extra) 'right 'same)]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['delta nat]]
                       (equality (add (multiply 'left 'factor) 'delta)
                                 finish))
         extra-product
         (transitive start combined finish distribute replace))))))})

(def multiply-left-monotone-spec
  (let [motive
        (function/lam
         [['factor nat]]
         (function/forall
          [['left nat] ['right nat]
           ['ordered (at-most 'left 'right)]]
          (at-most (multiply 'factor 'left)
                   (multiply 'factor 'right))))]
    {:name 'nat/multiply-left-monotone
     :universes []
     :type
     (function/forall
      [['factor nat] ['left nat] ['right nat]
       ['ordered (at-most 'left 'right)]]
      (at-most (multiply 'factor 'left) (multiply 'factor 'right)))
     :value
     (function/lam
      [['factor nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['left nat] ['right nat]
         ['ignored (at-most 'left 'right)]]
        (function/app (function/const* 'nat/at-most-reflexive []) zero))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['left nat] ['right nat]
         ['ordered (at-most 'left 'right)]]
        (function/app
         (function/const* 'nat/add-monotone [])
         'left 'right
         (multiply 'previous 'left) (multiply 'previous 'right)
         'ordered
         (function/app 'induction-hypothesis 'left 'right 'ordered)))
       'factor))}))

(def map-sum-monotone-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (at-most (map-sum 'A 'left 'source)
                  (map-sum 'A 'right 'source)))]
    {:name 'list/nat-map-sum-monotone
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['value 'A]]
         (at-most (function/app 'left 'value)
                  (function/app 'right 'value)))]
       ['source (list-of 'A)]]
      (at-most (map-sum 'A 'left 'source)
               (map-sum 'A 'right 'source)))
     :value
     (function/lam
      [['A type-u] ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['value 'A]]
         (at-most (function/app 'left 'value)
                  (function/app 'right 'value)))]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app (function/const* 'nat/at-most-reflexive []) zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (function/app
         (function/const* 'nat/add-monotone [])
         (function/app 'left 'head) (function/app 'right 'head)
         (map-sum 'A 'left 'tail) (map-sum 'A 'right 'tail)
         (function/app 'ordered 'head) 'induction-hypothesis))
       'source))}))

(def expectation-monotone-spec
  (let [left-map
        (function/lam
         [['state 'A]]
         (multiply (function/app 'left 'state)
                   (function/app 'mass 'state)))
        right-map
        (function/lam
         [['state 'A]]
         (multiply (function/app 'right 'state)
                   (function/app 'mass 'state)))]
    {:name 'probability/expectation-monotone
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['state 'A]]
         (at-most (function/app 'left 'state)
                  (function/app 'right 'state)))]]
      (at-most (expectation 'A 'source 'mass 'left)
               (expectation 'A 'source 'mass 'right)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['state 'A]]
         (at-most (function/app 'left 'state)
                  (function/app 'right 'state)))]]
      (function/app
       (function/const* 'list/nat-map-sum-monotone [U])
       'A left-map right-map
       (function/lam
        [['state 'A]]
        (function/app
         (function/const* 'nat/multiply-right-monotone [])
         (function/app 'mass 'state)
         (function/app 'left 'state) (function/app 'right 'state)
         (function/app 'ordered 'state)))
       (enumeration 'A 'source)))}))

(def theorem-specs
  [at-most-reflexive-spec at-most-transitive-spec at-most-successor-spec
   add-left-monotone-spec add-right-monotone-spec add-monotone-spec
   multiply-add-left-spec multiply-right-monotone-spec
   multiply-left-monotone-spec map-sum-monotone-spec
   expectation-monotone-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat order expression failed elaboration"
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
          {:origin :native :producer :constructive-nat-order}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat order theorem was rejected"
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
