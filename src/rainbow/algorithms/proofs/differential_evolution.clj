(ns rainbow.algorithms.proofs.differential-evolution
  "AHoF O44 Differential Evolution: the differential mutation over vector-valued
  population members. The DE/rand/1 mutation perturbs a base vector by a scaled
  difference of two other population vectors:

      donor = F * (b - c)
      mutant = base + donor

  Every term is an operation from the finite-vector capability (subtract, scale,
  add), so this reuses the n-dimensional vector state introduced for particle
  swarm. The scale factor is a general nonnegative rational; the population's
  stochastic index draws of the textbook algorithm are supplied as concrete
  population vectors in the worked instance, so what is proved is the
  deterministic mutation recurrence and a worked two-dimensional instance, not
  the stochastic population dynamics (which stay an executable-only concern).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.differential-evolution`
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

;; Vector-capability term builders (from rainbow.math.finite.vector).
(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (function/app (function/const* 'vector/subtract []) left right))
(defn- vector-scale [rate value]
  (function/app (function/const* 'vector/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- scaled-difference [f b c]
  (function/app (function/const* 'evolution/scaled-difference []) f b c))
(defn- differential-mutation [base f b c]
  (function/app (function/const* 'evolution/differential-mutation []) base f b c))

;; Definitions --------------------------------------------------------------

;; donor = F * (b - c)
(def scaled-difference-spec
  {:name 'evolution/scaled-difference :kind :definition :universes []
   :type (function/arrow nnrat vector-type vector-type vector-type)
   :value (function/lam [['f nnrat] ['b vector-type] ['c vector-type]]
                        (vector-scale 'f (vector-subtract 'b 'c)))})

;; mutant = base + F * (b - c)
(def differential-mutation-spec
  {:name 'evolution/differential-mutation :kind :definition :universes []
   :type (function/arrow vector-type nnrat vector-type vector-type vector-type)
   :value (function/lam [['base vector-type] ['f nnrat]
                         ['b vector-type] ['c vector-type]]
                        (vector-add 'base (scaled-difference 'f 'b 'c)))})

(def definition-specs [scaled-difference-spec differential-mutation-spec])

;; Theorems -----------------------------------------------------------------

;; The mutation unfolds to base plus the scaled difference.
(def mutation-unfold-spec
  {:name 'evolution/mutation-unfold :universes []
   :type (function/forall
          [['base vector-type] ['f nnrat]
           ['b vector-type] ['c vector-type]]
          (equality vector-type
                    (differential-mutation 'base 'f 'b 'c)
                    (vector-add 'base (scaled-difference 'f 'b 'c))))
   :value (function/lam [['base vector-type] ['f nnrat]
                         ['b vector-type] ['c vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (differential-mutation 'base 'f 'b 'c)))})

;; Worked two-dimensional mutation ------------------------------------------

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

;; Worked instance: the third vector is the origin so every difference keeps a
;; zero negative part, letting the whole trajectory reduce by reflexivity.
;;   scaled-difference: 2 * ([1,2] - [0,0]) = 2*[1,2] = [2,4]
;;   mutation: [0,0] + 1 * ([3,2] - [0,0]) = [0,0] + [3,2] = [3,2]
(def one-rational (nnrat-numeral 1))
(def two-rational (nnrat-numeral 2))
(def origin (make-vector (signed-numeral 0) (signed-numeral 0)))

(def scaled-difference-example-spec
  {:name 'evolution/scaled-difference-example :universes []
   :type (equality vector-type
                   (scaled-difference two-rational
                                      (make-vector (signed-numeral 1)
                                                   (signed-numeral 2))
                                      origin)
                   (make-vector (signed-numeral 2) (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (scaled-difference two-rational
                                           (make-vector (signed-numeral 1)
                                                        (signed-numeral 2))
                                           origin))})

(def mutation-example-spec
  {:name 'evolution/mutation-example :universes []
   :type (equality vector-type
                   (differential-mutation origin one-rational
                                          (make-vector (signed-numeral 3)
                                                       (signed-numeral 2))
                                          origin)
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (differential-mutation origin one-rational
                                               (make-vector (signed-numeral 3)
                                                            (signed-numeral 2))
                                               origin))})

;; A unit-scale mutation reduces to a plain vector sum of base and b.
(def unit-mutation-example-spec
  {:name 'evolution/unit-mutation-example :universes []
   :type (equality vector-type
                   (differential-mutation
                    (make-vector (signed-numeral 1) (signed-numeral 1))
                    one-rational
                    (make-vector (signed-numeral 2) (signed-numeral 3))
                    origin)
                   (make-vector (signed-numeral 3) (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (differential-mutation
                         (make-vector (signed-numeral 1) (signed-numeral 1))
                         one-rational
                         (make-vector (signed-numeral 2) (signed-numeral 3))
                         origin))})

(def theorem-specs
  [mutation-unfold-spec scaled-difference-example-spec
   mutation-example-spec unit-mutation-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :differential-evolution (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.differential-evolution))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
