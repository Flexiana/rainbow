(ns rainbow.math.rational.value
  "Exact nonnegative-rational worked values, proven through cross-product
  equivalence rather than pair equality.

  `nnrat/multiply` and `nnrat/add` are not definitionally reducible to a
  canonical `nnrat/make` pair, so a worked value like `1/2 * 1 = 1/2` cannot be
  proven by reflexivity on the pair. It CAN be proven on the equivalence
  relation: `nnrat/equivalent l r` is defined as the nat equality
  `numerator(l) * denominator(r) = numerator(r) * denominator(l)`, and nat
  multiplication does reduce, so each worked value below discharges by
  reflexivity on the reduced cross-product.

  This packages the reusable pattern: any exact rational worked value in an
  algorithm proof (cooling factors, learning rates, importance ratios, ...)
  should be stated with `nnrat/equivalent` and proven the same way, then carried
  by `nnrat/multiply-respects-equivalence` / `nnrat/add-respects-equivalence`."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))

(def half (function/const* 'nnrat/half []))
(def one (function/const* 'nnrat/one []))
(def quarter (function/const* 'nnrat/quarter []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
;; nnrat/make takes (numerator, denominator-PREDECESSOR); (whole n) = n/1.
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

;; The equivalence `left ~ right` reduces to
;;   numerator(left) * denominator(right) = numerator(right) * denominator(left)
;; so a reflexivity proof on the left cross-product discharges it whenever the
;; two cross-products reduce to the same nat.
(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

(defn- value-spec [name left right]
  {:name name :universes []
   :type (equivalent left right)
   :value (cross-product-reflexivity left right)})

;; Worked exact rational values ---------------------------------------------

;; 1/2 * 1 ~ 1/2
(def half-times-one-spec
  (value-spec 'rvalue/half-times-one (multiply half one) half))

;; 1/2 * 1/2 ~ 1/4
(def half-times-half-spec
  (value-spec 'rvalue/half-times-half (multiply half half) quarter))

;; 1/2 + 1/2 ~ 1
(def half-plus-half-spec
  (value-spec 'rvalue/half-plus-half (add half half) one))

;; 1/4 + 1/4 ~ 1/2
(def quarter-plus-quarter-spec
  (value-spec 'rvalue/quarter-plus-quarter (add quarter quarter) half))

;; 1 * 1/4 ~ 1/4
(def one-times-quarter-spec
  (value-spec 'rvalue/one-times-quarter (multiply one quarter) quarter))

;; Division also reduces cleanly, so ratio worked values (Newton/secant,
;; importance) are provable too.
;; 1 / (1/2) ~ 2
(def one-over-half-spec
  (value-spec 'rvalue/one-over-half (divide one half) (whole 2)))

;; (1/2) / (1/4) ~ 2
(def half-over-quarter-spec
  (value-spec 'rvalue/half-over-quarter (divide half quarter) (whole 2)))

;; (1/4) / (1/2) ~ 1/2
(def quarter-over-half-spec
  (value-spec 'rvalue/quarter-over-half (divide quarter half) half))

(def theorem-specs
  [half-times-one-spec half-times-half-spec half-plus-half-spec
   quarter-plus-quarter-spec one-times-quarter-spec
   one-over-half-spec half-over-quarter-spec quarter-over-half-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :rational-value theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
