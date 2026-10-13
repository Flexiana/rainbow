(ns rainbow.algorithms.proofs.cuckoo-search
  "AHoF O47 Cuckoo Search: the Levy-flight step over vector-valued state. A
  cuckoo lays an egg (a new candidate solution) by taking a scaled step from its
  current position in a random Levy-flight direction:

      position' = position + rate * direction

  a finite-vector scale and add. The heavy-tailed Levy direction and the nest
  abandonment / replacement (keep the better of the new and a random nest) are
  the sampler's and selector's concern (executable); the rate is a concrete
  nonnegative rational in the worked instance, so what is proved is the
  deterministic flight recurrence and worked instances.

  Requires the finite-vector capability.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.cuckoo-search`
  prints this classification."
  (:require [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [l r] (function/app (function/const* 'vector/add []) l r))
(defn- vector-scale [rate v]
  (function/app (function/const* 'vector/scale []) rate v))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nnrat-num [n] (function/app (function/const* 'nnrat/make [])
                                   (data-nat n) (data-nat 0)))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat []) (nnrat-num n)))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

(defn- levy-step [position rate direction]
  (function/app (function/const* 'cuckoo/levy-step []) position rate direction))

;; Definitions --------------------------------------------------------------

;; position' = position + rate * direction
(def levy-step-spec
  {:name 'cuckoo/levy-step :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type)
   :value (function/lam [['position vector-type] ['rate nnrat]
                         ['direction vector-type]]
                        (vector-add 'position
                                    (vector-scale 'rate 'direction)))})

(def definition-specs [levy-step-spec])

;; Theorems -----------------------------------------------------------------

(def levy-step-unfold-spec
  {:name 'cuckoo/levy-step-unfold :universes []
   :type (function/forall
          [['position vector-type] ['rate nnrat] ['direction vector-type]]
          (equality vector-type (levy-step 'position 'rate 'direction)
                    (vector-add 'position (vector-scale 'rate 'direction))))
   :value (function/lam [['position vector-type] ['rate nnrat]
                         ['direction vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (levy-step 'position 'rate 'direction)))})

;; A unit-rate flight from the origin in direction [3,2] lands at [3,2].
(def levy-step-example-spec
  {:name 'cuckoo/levy-step-example :universes []
   :type (equality vector-type
                   (levy-step (make-vector (signed-numeral 0) (signed-numeral 0))
                              (nnrat-num 1)
                              (make-vector (signed-numeral 3) (signed-numeral 2)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (levy-step
                         (make-vector (signed-numeral 0) (signed-numeral 0))
                         (nnrat-num 1)
                         (make-vector (signed-numeral 3) (signed-numeral 2))))})

;; A doubled flight: origin + 2 * [1,2] = [2,4].
(def scaled-flight-example-spec
  {:name 'cuckoo/scaled-flight-example :universes []
   :type (equality vector-type
                   (levy-step (make-vector (signed-numeral 0) (signed-numeral 0))
                              (nnrat-num 2)
                              (make-vector (signed-numeral 1) (signed-numeral 2)))
                   (make-vector (signed-numeral 2) (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (levy-step
                         (make-vector (signed-numeral 0) (signed-numeral 0))
                         (nnrat-num 2)
                         (make-vector (signed-numeral 1) (signed-numeral 2))))})

(def theorem-specs [levy-step-unfold-spec levy-step-example-spec
                    scaled-flight-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment checked-environment) :cuckoo-search
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
