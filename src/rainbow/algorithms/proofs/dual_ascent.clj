(ns rainbow.algorithms.proofs.dual-ascent
  "AHoF O52 Dual Ascent: the dual-variable ascent step over vector-valued
  multipliers. The dual function's gradient at the current point is the primal
  constraint residual r = A*x - b, so the multiplier ascends along it:

      lambda' = lambda + rate * residual

  Every term is a finite-vector operation (scale, add), reusing the n-dimensional
  vector state shared by the constraint methods. The inner primal minimization
  x*(lambda) = argmin_x L(x, lambda) and the residual r = A*x - b are problem
  data supplied to the step (matrix application and argmin are not exact-rational
  in general and stay an executable-only concern); what is proved here is the
  deterministic ascent recurrence and worked instances from a zero-initialized
  multiplier (the standard start for dual ascent), where a unit-rate step lands
  the multiplier exactly on the residual by reflexivity.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.dual-ascent`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- ascent-step [multiplier residual rate]
  (function/app (function/const* 'dual-ascent/ascent-step [])
                multiplier residual rate))

;; Definitions --------------------------------------------------------------

;; lambda' = lambda + rate * residual
(def ascent-step-spec
  {:name 'dual-ascent/ascent-step :kind :definition :universes []
   :type (function/arrow vector-type vector-type nnrat vector-type)
   :value (function/lam [['multiplier vector-type] ['residual vector-type]
                         ['rate nnrat]]
                        (vector-add 'multiplier
                                    (vector-scale 'rate 'residual)))})

(def definition-specs [ascent-step-spec])

;; Theorems -----------------------------------------------------------------

(def ascent-unfold-spec
  {:name 'dual-ascent/ascent-unfold :universes []
   :type (function/forall
          [['multiplier vector-type] ['residual vector-type] ['rate nnrat]]
          (equality vector-type
                    (ascent-step 'multiplier 'residual 'rate)
                    (vector-add 'multiplier
                                (vector-scale 'rate 'residual))))
   :value (function/lam [['multiplier vector-type] ['residual vector-type]
                         ['rate nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (ascent-step 'multiplier 'residual 'rate)))})

;; Worked ascent from a zero-initialized multiplier -------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-numeral [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-numeral n)))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

(def one-rational (nnrat-numeral 1))
(def zero-multiplier-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def zero-multiplier-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; From a zero multiplier a unit-rate step lands exactly on the residual:
;; [0,0] + 1 * [3,2] = [3,2].
(def unit-step-2d-example-spec
  {:name 'dual-ascent/unit-step-2d-example :universes []
   :type (equality vector-type
                   (ascent-step zero-multiplier-2d
                                (make-vector (signed-numeral 3)
                                             (signed-numeral 2))
                                one-rational)
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (ascent-step zero-multiplier-2d
                                     (make-vector (signed-numeral 3)
                                                  (signed-numeral 2))
                                     one-rational))})

;; The same in three dimensions: [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def unit-step-3d-example-spec
  {:name 'dual-ascent/unit-step-3d-example :universes []
   :type (equality vector-type
                   (ascent-step zero-multiplier-3d
                                (make-vector (signed-numeral 2)
                                             (signed-numeral 4)
                                             (signed-numeral 6))
                                one-rational)
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (ascent-step zero-multiplier-3d
                                     (make-vector (signed-numeral 2)
                                                  (signed-numeral 4)
                                                  (signed-numeral 6))
                                     one-rational))})

(def theorem-specs
  [ascent-unfold-spec unit-step-2d-example-spec unit-step-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :dual-ascent (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.dual-ascent))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
