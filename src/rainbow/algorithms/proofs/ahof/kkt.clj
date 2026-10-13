(ns rainbow.algorithms.proofs.ahof.kkt
  "AHoF O53 Lagrange Multipliers (KKT): the stationarity condition of the
  Karush-Kuhn-Tucker system. Reformulating a constrained problem as a system of
  equations, the Lagrangian gradient must vanish; for a single equality
  constraint the stationarity residual is

      stationarity gradF lambda gradG = gradF + lambda * gradG

  over the finite-vector state, and a KKT point is a (x, lambda) where this
  residual is the zero vector. Every term is an exact finite-vector operation
  (scale, add), reusing the shared n-dimensional vector state. The gradients
  gradF, gradG and the multiplier lambda are problem data (differentiation and
  the root solve are executable / not exact-rational in general); what is proved
  here is the deterministic stationarity combination and a worked instance where
  a zero objective gradient makes the residual land exactly on lambda * gradG.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kkt`
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

(defn- stationarity [grad-f lambda grad-g]
  (function/app (function/const* 'kkt/stationarity []) grad-f lambda grad-g))

;; Definitions --------------------------------------------------------------

;; stationarity gradF lambda gradG = gradF + lambda * gradG
(def stationarity-spec
  {:name 'kkt/stationarity :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['grad-f vector-type] ['lambda nnrat]
                         ['grad-g vector-type]]
                        (vector-add 'grad-f
                                    (vector-scale 'lambda 'grad-g)))})

(def definition-specs [stationarity-spec])

;; Theorems -----------------------------------------------------------------

(def stationarity-unfold-spec
  {:name 'kkt/stationarity-unfold :universes []
   :type (function/forall
          [['grad-f vector-type] ['lambda nnrat] ['grad-g vector-type]]
          (equality vector-type
                    (stationarity 'grad-f 'lambda 'grad-g)
                    (vector-add 'grad-f (vector-scale 'lambda 'grad-g))))
   :value (function/lam [['grad-f vector-type] ['lambda nnrat]
                         ['grad-g vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (stationarity 'grad-f 'lambda 'grad-g)))})

;; Worked stationarity from a zero objective gradient ------------------------

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
(def zero-grad-2d (make-vector (signed-numeral 0) (signed-numeral 0)))

;; With a vanishing objective gradient and unit multiplier, stationarity is the
;; constraint gradient itself: [0,0] + 1 * [3,2] = [3,2].
(def stationarity-example-spec
  {:name 'kkt/stationarity-example :universes []
   :type (equality vector-type
                   (stationarity zero-grad-2d one-rational
                                 (make-vector (signed-numeral 3)
                                              (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (stationarity zero-grad-2d one-rational
                                      (make-vector (signed-numeral 3)
                                                   (signed-numeral 2))))})

;; The three-dimensional analogue: [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def stationarity-3d-example-spec
  {:name 'kkt/stationarity-3d-example :universes []
   :type (equality vector-type
                   (stationarity
                    (make-vector (signed-numeral 0) (signed-numeral 0)
                                 (signed-numeral 0))
                    one-rational
                    (make-vector (signed-numeral 2) (signed-numeral 4)
                                 (signed-numeral 6)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (stationarity
                         (make-vector (signed-numeral 0) (signed-numeral 0)
                                      (signed-numeral 0))
                         one-rational
                         (make-vector (signed-numeral 2) (signed-numeral 4)
                                      (signed-numeral 6))))})

(def theorem-specs
  [stationarity-unfold-spec stationarity-example-spec
   stationarity-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-kkt (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.kkt))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
