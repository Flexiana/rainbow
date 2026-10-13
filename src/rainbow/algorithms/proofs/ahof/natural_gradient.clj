(ns rainbow.algorithms.proofs.ahof.natural-gradient
  "AHoF D50 Natural Gradient: the policy update that ascends along the natural
  gradient -- the ordinary gradient preconditioned by the inverse Fisher
  information matrix, so the step is invariant to the parameterization of the
  policy. Given the natural-gradient direction (F^{-1} grad, supplied as problem
  data), the parameters update by:

      update theta rate natural = theta + rate * natural

  over the finite-vector parameter state. The Fisher-information estimate and its
  inversion are executable / not exact-rational concerns; what is proved here is
  the deterministic natural-gradient update recurrence and worked instances from
  a zero-initialized parameter, where a unit-rate step lands exactly on the
  natural-gradient direction.

  Requires the shared finite-vector operations (vector/add, vector/scale) over
  signed rationals -- carried by the D63 checkpoint via the vector layer.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.natural-gradient`
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

(defn- update-step [theta rate natural]
  (function/app (function/const* 'natural-gradient/update []) theta rate natural))

;; Definitions --------------------------------------------------------------

;; update theta rate natural = theta + rate * natural
(def update-spec
  {:name 'natural-gradient/update :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['theta vector-type] ['rate nnrat]
                         ['natural vector-type]]
                        (vector-add 'theta (vector-scale 'rate 'natural)))})

(def definition-specs [update-spec])

;; Theorems -----------------------------------------------------------------

(def update-unfold-spec
  {:name 'natural-gradient/update-unfold :universes []
   :type (function/forall
          [['theta vector-type] ['rate nnrat] ['natural vector-type]]
          (equality vector-type
                    (update-step 'theta 'rate 'natural)
                    (vector-add 'theta (vector-scale 'rate 'natural))))
   :value (function/lam [['theta vector-type] ['rate nnrat]
                         ['natural vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (update-step 'theta 'rate 'natural)))})

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
(def zero-theta-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def zero-theta-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; [0,0] + 1 * [3,2] = [3,2].
(def update-unit-2d-example-spec
  {:name 'natural-gradient/update-unit-2d-example :universes []
   :type (equality vector-type
                   (update-step zero-theta-2d one-rational
                                (make-vector (signed-numeral 3)
                                             (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (update-step zero-theta-2d one-rational
                                     (make-vector (signed-numeral 3)
                                                  (signed-numeral 2))))})

;; [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def update-unit-3d-example-spec
  {:name 'natural-gradient/update-unit-3d-example :universes []
   :type (equality vector-type
                   (update-step zero-theta-3d one-rational
                                (make-vector (signed-numeral 2)
                                             (signed-numeral 4)
                                             (signed-numeral 6)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (update-step zero-theta-3d one-rational
                                     (make-vector (signed-numeral 2)
                                                  (signed-numeral 4)
                                                  (signed-numeral 6))))})

(def theorem-specs
  [update-unfold-spec update-unit-2d-example-spec update-unit-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-natural-gradient (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.natural-gradient))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
