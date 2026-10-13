(ns rainbow.algorithms.proofs.ahof.cmaes
  "AHoF O42 CMA-ES (Covariance Matrix Adaptation Evolution Strategy) -- the mean
  recombination step. Each generation, the new distribution mean is the weighted
  recombination of the selected (elite) samples, ranked best first:

      recombine w1 x1 w2 x2 = w1 * x1 + w2 * x2

  over the finite-vector search state (two elite; the general case folds this
  over all selected samples with the CMA recombination weights). The
  rank-one/rank-mu covariance-matrix updates and the step-size adaptation
  (involving eigen-decompositions and square roots) are executable / not
  exact-rational concerns; the recombination weights are supplied rationals
  summing to one. What is proved here is the deterministic weighted recombination
  and worked instances from a convex combination.

  Requires the shared finite-vector operations (vector/add, vector/scale) over
  signed rationals -- carried by the D63 checkpoint via the vector layer.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cmaes`
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

(defn- recombine [w1 x1 w2 x2]
  (function/app (function/const* 'cmaes/recombine []) w1 x1 w2 x2))

;; Definitions --------------------------------------------------------------

;; recombine w1 x1 w2 x2 = w1 * x1 + w2 * x2
(def recombine-spec
  {:name 'cmaes/recombine :kind :definition :universes []
   :type (function/arrow nnrat vector-type nnrat vector-type vector-type)
   :value (function/lam [['w1 nnrat] ['x1 vector-type]
                         ['w2 nnrat] ['x2 vector-type]]
                        (vector-add (vector-scale 'w1 'x1)
                                    (vector-scale 'w2 'x2)))})

(def definition-specs [recombine-spec])

;; Theorems -----------------------------------------------------------------

(def recombine-unfold-spec
  {:name 'cmaes/recombine-unfold :universes []
   :type (function/forall
          [['w1 nnrat] ['x1 vector-type] ['w2 nnrat] ['x2 vector-type]]
          (equality vector-type
                    (recombine 'w1 'x1 'w2 'x2)
                    (vector-add (vector-scale 'w1 'x1)
                                (vector-scale 'w2 'x2))))
   :value (function/lam [['w1 nnrat] ['x1 vector-type]
                         ['w2 nnrat] ['x2 vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type
                         (recombine 'w1 'x1 'w2 'x2)))})

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

;; Recombine the top elite alone (second weight 0): weight the best fully.
;; 1 * [3,2] + 0 * [5,5] = [3,2].
(def recombine-top-example-spec
  {:name 'cmaes/recombine-top-example :universes []
   :type (equality vector-type
                   (recombine (nnrat-numeral 1)
                              (make-vector (signed-numeral 3) (signed-numeral 2))
                              (nnrat-numeral 0)
                              (make-vector (signed-numeral 5) (signed-numeral 5)))
                   (make-vector (signed-numeral 3) (signed-numeral 2)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (recombine (nnrat-numeral 1)
                                   (make-vector (signed-numeral 3)
                                                (signed-numeral 2))
                                   (nnrat-numeral 0)
                                   (make-vector (signed-numeral 5)
                                                (signed-numeral 5))))})

;; Equal-weight recombination of scaled elite: 2 * [3,2] + 1 * [1,4] = [7,8].
(def recombine-example-spec
  {:name 'cmaes/recombine-example :universes []
   :type (equality vector-type
                   (recombine (nnrat-numeral 2)
                              (make-vector (signed-numeral 3) (signed-numeral 2))
                              (nnrat-numeral 1)
                              (make-vector (signed-numeral 1) (signed-numeral 4)))
                   (make-vector (signed-numeral 7) (signed-numeral 8)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (recombine (nnrat-numeral 2)
                                   (make-vector (signed-numeral 3)
                                                (signed-numeral 2))
                                   (nnrat-numeral 1)
                                   (make-vector (signed-numeral 1)
                                                (signed-numeral 4))))})

(def theorem-specs
  [recombine-unfold-spec recombine-top-example-spec recombine-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-cmaes (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.cmaes))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
