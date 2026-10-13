(ns rainbow.algorithms.proofs.noisy-descent
  "AHoF O38 Noisy Descent: the WRAP pattern that perturbs a base descent step
  with additive noise. Given whatever step a base optimizer produced, the noisy
  wrapper adds a perturbation vector:

      wrapped = step + noise

  This is a finite-vector addition; the base step and the noise draw are the
  wrapped optimizer's and the sampler's concern (executable), and the textbook
  Gaussian perturbation is supplied as a concrete vector in the worked instance.
  What is proved here is the wrap recurrence and worked instances.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.noisy-descent`
  prints this classification."
  (:require [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [left right]
  (function/app (function/const* 'vector/add []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- wrap [step noise]
  (function/app (function/const* 'noisy/wrap []) step noise))

;; Definitions --------------------------------------------------------------

;; Perturb a base step with additive noise.
(def wrap-spec
  {:name 'noisy/wrap :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['step vector-type] ['noise vector-type]]
                        (vector-add 'step 'noise))})

(def definition-specs [wrap-spec])

;; Theorems -----------------------------------------------------------------

(def wrap-unfold-spec
  {:name 'noisy/wrap-unfold :universes []
   :type (function/forall
          [['step vector-type] ['noise vector-type]]
          (equality vector-type (wrap 'step 'noise)
                    (vector-add 'step 'noise)))
   :value (function/lam [['step vector-type] ['noise vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (wrap 'step 'noise)))})

;; Worked instances ---------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

;; A base step [1,2] perturbed by noise [1,1] becomes [2,3].
(def wrap-example-spec
  {:name 'noisy/wrap-example :universes []
   :type (equality vector-type
                   (wrap (make-vector (signed-numeral 1) (signed-numeral 2))
                         (make-vector (signed-numeral 1) (signed-numeral 1)))
                   (make-vector (signed-numeral 2) (signed-numeral 3)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (wrap (make-vector (signed-numeral 1) (signed-numeral 2))
                              (make-vector (signed-numeral 1)
                                           (signed-numeral 1))))})

;; A three-dimensional perturbation: [1,2,3] + [1,1,1] = [2,3,4].
(def wrap-3d-example-spec
  {:name 'noisy/wrap-3d-example :universes []
   :type (equality vector-type
                   (wrap (make-vector (signed-numeral 1) (signed-numeral 2)
                                      (signed-numeral 3))
                         (make-vector (signed-numeral 1) (signed-numeral 1)
                                      (signed-numeral 1)))
                   (make-vector (signed-numeral 2) (signed-numeral 3)
                                (signed-numeral 4)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        vector-type
                        (wrap (make-vector (signed-numeral 1) (signed-numeral 2)
                                           (signed-numeral 3))
                              (make-vector (signed-numeral 1) (signed-numeral 1)
                                           (signed-numeral 1))))})

(def theorem-specs
  [wrap-unfold-spec wrap-example-spec wrap-3d-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment checked-environment) :noisy-descent
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
