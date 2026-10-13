(ns rainbow.math.finite.vector
  "Finite vectors over signed rationals: lists of signed-rational components with
  elementwise addition, negation, subtraction, and scalar scaling. This is the
  first genuinely n-dimensional state in the corpus, the foundation for
  multi-dimensional optimization and filtering. Scaling and negation reuse the
  list map; elementwise addition is a zip of the two component lists via the list
  recursor."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- nil-vector []
  (function/app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (function/app (function/const* 'data/cons [type-level]) signed head tail))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- list-map [f xs]
  (function/app (function/const* 'list/map [type-level type-level])
                signed signed f xs))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-negate [value]
  (function/app (function/const* 'vector/negate []) value))
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))

;; Definitions --------------------------------------------------------------

;; Scale every component by a nonnegative-rational factor.
(def scale-spec
  {:name 'vector/scale :kind :definition :universes []
   :type (function/arrow nnrat vector-type vector-type)
   :value (function/lam [['rate nnrat] ['components vector-type]]
                        (list-map (function/lam [['component signed]]
                                                (signed-scale 'rate 'component))
                                  'components))})

;; Negate every component.
(def negate-spec
  {:name 'vector/negate :kind :definition :universes []
   :type (function/arrow vector-type vector-type)
   :value (function/lam [['components vector-type]]
                        (list-map (function/lam [['component signed]]
                                                (signed-negate 'component))
                                  'components))})

;; Elementwise addition: zip the two component lists with signed addition.
(def add-spec
  {:name 'vector/add :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (function/app
     (function/app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam [['ignored vector-type]]
                    (function/arrow vector-type vector-type))
      (function/lam [['other vector-type]] (nil-vector))
      (function/lam
       [['head signed] ['tail vector-type]
        ['recur (function/arrow vector-type vector-type)]]
       (function/lam
        [['other vector-type]]
        (function/app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] vector-type)
         (nil-vector)
         (function/lam
          [['other-head signed] ['other-tail vector-type]
           ['ignored-recur vector-type]]
          (cons-vector (signed-add 'head 'other-head)
                       (function/app 'recur 'other-tail)))
         'other)))
      'left)
     'right))})

;; Elementwise subtraction: add the negation.
(def subtract-spec
  {:name 'vector/subtract :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['left vector-type] ['right vector-type]]
                        (vector-add 'left (vector-negate 'right)))})

(def definition-specs [scale-spec negate-spec add-spec subtract-spec])

;; Theorems -----------------------------------------------------------------

;; Adding the empty vector on the left is empty (the zip stops at the shorter).
(def add-nil-spec
  {:name 'vector/add-nil :universes []
   :type (function/forall
          [['right vector-type]]
          (equality vector-type (vector-add (nil-vector) 'right) (nil-vector)))
   :value (function/lam [['right vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (nil-vector)))})

;; Subtraction unfolds to addition of the negation.
(def subtract-unfold-spec
  {:name 'vector/subtract-unfold :universes []
   :type (function/forall
          [['left vector-type] ['right vector-type]]
          (equality vector-type (vector-subtract 'left 'right)
                    (vector-add 'left (vector-negate 'right))))
   :value (function/lam [['left vector-type] ['right vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (vector-subtract 'left 'right)))})

;; Worked component arithmetic ---------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- make-vector [& components]
  (reduce (fn [tail component] (cons-vector component tail))
          (nil-vector) (reverse components)))
(def two-rational
  (function/app (function/const* 'nnrat/make []) (data-nat 2) (data-nat 0)))

;; Elementwise addition of two-component vectors: [1,2] + [3,4] = [4,6].
(def add-example-spec
  {:name 'vector/add-example :universes []
   :type (equality vector-type
                   (vector-add (make-vector (signed-numeral 1) (signed-numeral 2))
                               (make-vector (signed-numeral 3) (signed-numeral 4)))
                   (make-vector (signed-numeral 4) (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (vector-add
                         (make-vector (signed-numeral 1) (signed-numeral 2))
                         (make-vector (signed-numeral 3) (signed-numeral 4))))})

;; Scalar scaling of a vector: 2 * [1,2] = [2,4].
(def scale-example-spec
  {:name 'vector/scale-example :universes []
   :type (equality vector-type
                   (vector-scale two-rational
                                 (make-vector (signed-numeral 1)
                                              (signed-numeral 2)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (vector-scale two-rational
                                      (make-vector (signed-numeral 1)
                                                   (signed-numeral 2))))})

;; A three-dimensional elementwise sum: [1,2,3] + [3,4,5] = [4,6,8].
(def add-example-3d-spec
  {:name 'vector/add-example-3d :universes []
   :type (equality vector-type
                   (vector-add
                    (make-vector (signed-numeral 1) (signed-numeral 2)
                                 (signed-numeral 3))
                    (make-vector (signed-numeral 3) (signed-numeral 4)
                                 (signed-numeral 5)))
                   (make-vector (signed-numeral 4) (signed-numeral 6)
                                (signed-numeral 8)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (vector-add
                         (make-vector (signed-numeral 1) (signed-numeral 2)
                                      (signed-numeral 3))
                         (make-vector (signed-numeral 3) (signed-numeral 4)
                                      (signed-numeral 5))))})

(def theorem-specs
  [add-nil-spec subtract-unfold-spec add-example-spec scale-example-spec
   add-example-3d-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-vector expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec* [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :finite-vector}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-vector declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec* checked-environment
          (concat definition-specs theorem-specs)))

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
