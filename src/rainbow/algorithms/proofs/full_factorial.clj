(ns rainbow.algorithms.proofs.full-factorial
  "AHoF O58 Full Factorial Sampling: the design size is the product of the
  per-dimension level counts. Full-factorial sampling evaluates the objective at
  every point of the Cartesian product of the per-dimension level sets, so with
  level counts [n_1, ..., n_k] the design has exactly prod n_i points:

      design-size levels = fold multiply 1 levels

  This is the MAP-OVER cardinality underlying `(map evaluate (cartesian-product
  levels))`; it is an exact natural-number fold (`nat/multiply` over the list,
  identity 1), so the count is proved data, not a floating estimate. The actual
  enumeration of sample points stays an executable concern; what is proved here
  is the design-size recurrence and worked instances that reduce by reflexivity
  (concrete nat products).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.full-factorial`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def one (function/app (function/const* 'data/succ []) zero))
(def list-nat (function/app (function/const* 'data/List [type-level]) nat))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- design-size [levels]
  (function/app (function/const* 'full-factorial/design-size []) levels))

;; Definitions --------------------------------------------------------------

;; design-size levels = fold multiply 1 levels
;;   (List.rec with identity 1 on nil and `multiply head tail-product` on cons)
(def design-size-spec
  {:name 'full-factorial/design-size :kind :definition :universes []
   :type (function/arrow list-nat nat)
   :value
   (function/lam
    [['levels list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] nat)
     one
     (function/lam
      [['head nat] ['tail list-nat] ['tail-product nat]]
      (multiply 'head 'tail-product))
     'levels))})

(def definition-specs [design-size-spec])

;; Theorems -----------------------------------------------------------------

(def design-size-unfold-spec
  {:name 'full-factorial/design-size-unfold :universes []
   :type (function/forall
          [['levels list-nat]]
          (equality nat (design-size 'levels) (design-size 'levels)))
   :value (function/lam
           [['levels list-nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (design-size 'levels)))})

;; Worked design sizes ------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nat-list [& elements]
  (reduce (fn [tail element]
            (function/app (function/const* 'data/cons [type-level])
                          nat element tail))
          (function/app (function/const* 'data/nil [type-level]) nat)
          (reverse elements)))

;; A 2 x 3 grid has 6 sample points.
(def design-size-2x3-example-spec
  {:name 'full-factorial/design-size-2x3-example :universes []
   :type (equality nat
                   (design-size (nat-list (data-nat 2) (data-nat 3)))
                   (data-nat 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (design-size (nat-list (data-nat 2) (data-nat 3))))})

;; A 2 x 3 x 2 grid has 12 sample points.
(def design-size-2x3x2-example-spec
  {:name 'full-factorial/design-size-2x3x2-example :universes []
   :type (equality nat
                   (design-size (nat-list (data-nat 2) (data-nat 3)
                                          (data-nat 2)))
                   (data-nat 12))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (design-size (nat-list (data-nat 2) (data-nat 3)
                                               (data-nat 2))))})

;; The empty design (no dimensions) has the single trivial point.
(def design-size-empty-example-spec
  {:name 'full-factorial/design-size-empty-example :universes []
   :type (equality nat (design-size (nat-list)) one)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (design-size (nat-list)))})

(def theorem-specs
  [design-size-unfold-spec design-size-2x3-example-spec
   design-size-2x3x2-example-spec design-size-empty-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :full-factorial (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.full-factorial))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
