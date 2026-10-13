(ns rainbow.algorithms.proofs.ahof.mesh-adaptive
  "AHoF O39 Mesh Adaptive Direct Search (MADS): a derivative-free direct-search
  method that probes the objective at mesh points around the incumbent. Each poll
  step steps from the current point along a poll direction by the current mesh
  size:

      poll x delta direction = x + delta * direction

  over the finite-vector state. When a poll point improves the objective the mesh
  is coarsened; otherwise it is refined -- an executable control concern. The poll
  directions are drawn to grow dense on the unit sphere (the property that makes
  MADS convergent), also executable. What is proved here is the deterministic
  poll-step recurrence and worked instances from a zero incumbent, where a unit
  mesh step lands exactly on the poll direction.

  Requires the shared finite-vector operations (vector/add, vector/scale) over
  signed rationals -- carried by the D63 checkpoint via the vector layer.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mesh-adaptive`
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

(defn- poll [x delta direction]
  (function/app (function/const* 'mads/poll []) x delta direction))

;; Definitions --------------------------------------------------------------

;; poll x delta direction = x + delta * direction
(def poll-spec
  {:name 'mads/poll :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['x vector-type] ['delta nnrat]
                         ['direction vector-type]]
                        (vector-add 'x (vector-scale 'delta 'direction)))})

(def definition-specs [poll-spec])

;; Theorems -----------------------------------------------------------------

(def poll-unfold-spec
  {:name 'mads/poll-unfold :universes []
   :type (function/forall
          [['x vector-type] ['delta nnrat] ['direction vector-type]]
          (equality vector-type
                    (poll 'x 'delta 'direction)
                    (vector-add 'x (vector-scale 'delta 'direction))))
   :value (function/lam [['x vector-type] ['delta nnrat]
                         ['direction vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (poll 'x 'delta 'direction)))})

;; Worked poll from a zero incumbent ----------------------------------------

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
(def origin-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def origin-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; A unit mesh step from the origin lands on the poll direction:
;; [0,0] + 1 * [3,2] = [3,2].
(def poll-unit-2d-example-spec
  {:name 'mads/poll-unit-2d-example :universes []
   :type (equality vector-type
                   (poll origin-2d one-rational
                         (make-vector (signed-numeral 3) (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (poll origin-2d one-rational
                              (make-vector (signed-numeral 3)
                                           (signed-numeral 2))))})

;; The same in three dimensions: [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def poll-unit-3d-example-spec
  {:name 'mads/poll-unit-3d-example :universes []
   :type (equality vector-type
                   (poll origin-3d one-rational
                         (make-vector (signed-numeral 2) (signed-numeral 4)
                                      (signed-numeral 6)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (poll origin-3d one-rational
                              (make-vector (signed-numeral 2) (signed-numeral 4)
                                           (signed-numeral 6))))})

(def theorem-specs
  [poll-unfold-spec poll-unit-2d-example-spec poll-unit-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-mesh-adaptive (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.mesh-adaptive))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
