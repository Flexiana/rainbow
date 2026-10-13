(ns rainbow.algorithms.proofs.inner-product
  "The vector dot product (inner product) over signed-rational vectors:

      dot [a1..an] [b1..bn] = sum_i a_i * b_i

  This is a zip of the two component lists with signed multiplication, summed
  with signed addition -- a nested `data/List.rec` that reduces the two vectors
  to a single signed scalar (the shape of `vector/add`, but accumulating a sum of
  products rather than a vector). It reuses `signed/multiply` and unblocks
  inner-product methods: hypergradient learning-rate updates, cosine similarity,
  and conjugate-gradient direction tests.

  Requires `signed/multiply` (from rainbow.math.rational.signed.multiply) in the
  environment.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.inner-product`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.rational.signed.multiply :as dep-signed-multiply]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- signed-zero [] (function/const* 'signed/zero []))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (function/app (function/const* 'signed/multiply []) left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- nnrat-num [n] (function/app (function/const* 'nnrat/make [])
                                   (data-nat n) (data-nat 0)))
(defn- signed-make [p n] (function/app (function/const* 'signed/make []) p n))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))

(defn- dot [left right]
  (function/app (function/const* 'vector/dot []) left right))

;; A signed worked value proven by reflexivity on the reduced nat cross-product.
(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

;; dot = nested List.rec zip-and-sum of the two component lists.
(def dot-spec
  {:name 'vector/dot :kind :definition :universes []
   :type (function/arrow vector-type vector-type signed)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (function/app
     (function/app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam [['ignored vector-type]] (function/arrow vector-type signed))
      (function/lam [['other vector-type]] (signed-zero))
      (function/lam
       [['head signed] ['tail vector-type]
        ['recur (function/arrow vector-type signed)]]
       (function/lam
        [['other vector-type]]
        (function/app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] signed)
         (signed-zero)
         (function/lam
          [['other-head signed] ['other-tail vector-type]
           ['ignored-recur signed]]
          (signed-add (signed-multiply 'head 'other-head)
                      (function/app 'recur 'other-tail)))
         'other)))
      'left)
     'right))})

(def definition-specs [dot-spec])

;; Theorems -----------------------------------------------------------------

;; The dot product of empty vectors is zero.
(def dot-nil-spec
  {:name 'vector/dot-nil :universes []
   :type (signed-equivalent
          (dot (function/app (function/const* 'data/nil [type-level]) signed)
               (function/app (function/const* 'data/nil [type-level]) signed))
          (signed-zero))
   :value (signed-cross-reflexivity
           (dot (function/app (function/const* 'data/nil [type-level]) signed)
                (function/app (function/const* 'data/nil [type-level]) signed))
           (signed-zero))})

;; [2,3] . [1,2] = 2*1 + 3*2 = 8.
(def dot-example-spec
  {:name 'vector/dot-example :universes []
   :type (signed-equivalent
          (dot (make-vector (signed-numeral 2) (signed-numeral 3))
               (make-vector (signed-numeral 1) (signed-numeral 2)))
          (signed-numeral 8))
   :value (signed-cross-reflexivity
           (dot (make-vector (signed-numeral 2) (signed-numeral 3))
                (make-vector (signed-numeral 1) (signed-numeral 2)))
           (signed-numeral 8))})

;; A three-dimensional inner product: [1,2,3] . [1,1,1] = 1 + 2 + 3 = 6.
(def dot-3d-example-spec
  {:name 'vector/dot-3d-example :universes []
   :type (signed-equivalent
          (dot (make-vector (signed-numeral 1) (signed-numeral 2)
                            (signed-numeral 3))
               (make-vector (signed-numeral 1) (signed-numeral 1)
                            (signed-numeral 1)))
          (signed-numeral 6))
   :value (signed-cross-reflexivity
           (dot (make-vector (signed-numeral 1) (signed-numeral 2)
                             (signed-numeral 3))
                (make-vector (signed-numeral 1) (signed-numeral 1)
                             (signed-numeral 1)))
           (signed-numeral 6))})

(def theorem-specs [dot-nil-spec dot-example-spec dot-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :inner-product (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.inner-product))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
