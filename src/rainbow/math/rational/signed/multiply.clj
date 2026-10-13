(ns rainbow.math.rational.signed.multiply
  "Signed-rational multiplication, extending the addition-only signed rationals.
  A signed rational is a Grothendieck pair (positive, negative); the product is

      (p1, n1) * (p2, n2) = (p1*p2 + n1*n2, p1*n2 + n1*p2)

  which is the usual sign rule expressed on the pair, built from nonnegative
  rational multiplication and addition without any new kernel rule. Worked values
  are proved on the signed cross-product equivalence (`signed/equivalent`), so
  they discharge by reflexivity on the reduced nat cross-product. This unblocks
  inner products, so dot-product and hypergradient methods become expressible."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- signed-make [positive negative]
  (function/app (function/const* 'signed/make []) positive negative))
(defn- nnrat-num [n] (function/app (function/const* 'nnrat/make [])
                                   (data-nat n) (data-nat 0)))

(defn- s-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- s-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- signed-multiply [left right]
  (function/app (function/const* 'signed/multiply []) left right))

;; The signed equivalence `left ~ right` unfolds to the nnrat equivalence
;;   positive(left) + negative(right)  ~  positive(right) + negative(left)
;; which unfolds to the nat cross-product equality; a reflexivity proof on the
;; left cross-product discharges it when both sides reduce to the same nat.
(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

(def multiply-spec
  {:name 'signed/multiply :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam
           [['left signed] ['right signed]]
           (signed-make
            (nnrat-add (nnrat-multiply (s-positive 'left) (s-positive 'right))
                       (nnrat-multiply (s-negative 'left) (s-negative 'right)))
            (nnrat-add (nnrat-multiply (s-positive 'left) (s-negative 'right))
                       (nnrat-multiply (s-negative 'left) (s-positive 'right)))))})

(def definition-specs [multiply-spec])

;; Theorems -----------------------------------------------------------------

(def multiply-unfold-spec
  {:name 'signed/multiply-unfold :universes []
   :type (function/forall
          [['left signed] ['right signed]]
          (equality signed (signed-multiply 'left 'right)
                    (signed-make
                     (nnrat-add
                      (nnrat-multiply (s-positive 'left) (s-positive 'right))
                      (nnrat-multiply (s-negative 'left) (s-negative 'right)))
                     (nnrat-add
                      (nnrat-multiply (s-positive 'left) (s-negative 'right))
                      (nnrat-multiply (s-negative 'left) (s-positive 'right))))))
   :value (function/lam [['left signed] ['right signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (signed-multiply 'left 'right)))})

;; 2 * 3 ~ 6.
(def two-times-three-spec
  {:name 'signed/multiply-two-times-three :universes []
   :type (signed-equivalent (signed-multiply (signed-numeral 2) (signed-numeral 3))
                            (signed-numeral 6))
   :value (signed-cross-reflexivity
           (signed-multiply (signed-numeral 2) (signed-numeral 3))
           (signed-numeral 6))})

;; (-2) * 3 ~ -6  (negative times positive is negative).
(def negative-two-times-three-spec
  (let [minus-two (signed-make (nnrat-num 0) (nnrat-num 2))
        minus-six (signed-make (nnrat-num 0) (nnrat-num 6))]
    {:name 'signed/multiply-negative-two-times-three :universes []
     :type (signed-equivalent (signed-multiply minus-two (signed-numeral 3))
                              minus-six)
     :value (signed-cross-reflexivity
             (signed-multiply minus-two (signed-numeral 3)) minus-six)}))

(def theorem-specs
  [multiply-unfold-spec two-times-three-spec negative-two-times-three-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :signed-multiply
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
