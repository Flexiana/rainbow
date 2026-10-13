(ns rainbow.algorithms.proofs.ahof.hmc
  "AHoF V24 Hamiltonian Monte Carlo -- the leapfrog integrator that simulates
  Hamiltonian dynamics to make distant, high-acceptance proposals. Leapfrog
  alternates a full position drift with momentum half-kicks; the position drift
  moves the state by the step size times the (mass-scaled) momentum:

      drift q step momentum = q + step * momentum

  over the finite-vector state. The potential-energy gradient (the momentum kick
  -step/2 * gradU) and the Metropolis-Hastings accept/reject on the Hamiltonian
  are separate concerns (the gradient is supplied; the accept test is
  ahof-metropolis / executable). What is proved here is the deterministic
  position-drift recurrence and worked instances from a zero position, where a
  unit step lands exactly on the momentum.

  Requires the shared finite-vector operations (vector/add, vector/scale) over
  signed rationals -- carried by the D63 checkpoint via the vector layer.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hmc`
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

(defn- drift [q step momentum]
  (function/app (function/const* 'hmc/drift []) q step momentum))

;; Definitions --------------------------------------------------------------

;; drift q step momentum = q + step * momentum  (leapfrog position update)
(def drift-spec
  {:name 'hmc/drift :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['q vector-type] ['step nnrat]
                         ['momentum vector-type]]
                        (vector-add 'q (vector-scale 'step 'momentum)))})

(def definition-specs [drift-spec])

;; Theorems -----------------------------------------------------------------

(def drift-unfold-spec
  {:name 'hmc/drift-unfold :universes []
   :type (function/forall
          [['q vector-type] ['step nnrat] ['momentum vector-type]]
          (equality vector-type
                    (drift 'q 'step 'momentum)
                    (vector-add 'q (vector-scale 'step 'momentum))))
   :value (function/lam [['q vector-type] ['step nnrat]
                         ['momentum vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (drift 'q 'step 'momentum)))})

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
(def zero-q-2d (make-vector (signed-numeral 0) (signed-numeral 0)))
(def zero-q-3d
  (make-vector (signed-numeral 0) (signed-numeral 0) (signed-numeral 0)))

;; A unit-step drift from a zero position lands on the momentum:
;; [0,0] + 1 * [3,2] = [3,2].
(def drift-unit-2d-example-spec
  {:name 'hmc/drift-unit-2d-example :universes []
   :type (equality vector-type
                   (drift zero-q-2d one-rational
                          (make-vector (signed-numeral 3) (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (drift zero-q-2d one-rational
                               (make-vector (signed-numeral 3)
                                            (signed-numeral 2))))})

;; The same in three dimensions: [0,0,0] + 1 * [2,4,6] = [2,4,6].
(def drift-unit-3d-example-spec
  {:name 'hmc/drift-unit-3d-example :universes []
   :type (equality vector-type
                   (drift zero-q-3d one-rational
                          (make-vector (signed-numeral 2) (signed-numeral 4)
                                       (signed-numeral 6)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)
                                (signed-numeral 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (drift zero-q-3d one-rational
                               (make-vector (signed-numeral 2) (signed-numeral 4)
                                            (signed-numeral 6))))})

(def theorem-specs
  [drift-unfold-spec drift-unit-2d-example-spec drift-unit-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-hmc (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.hmc))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
