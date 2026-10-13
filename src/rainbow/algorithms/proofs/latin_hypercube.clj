(ns rainbow.algorithms.proofs.latin-hypercube
  "AHoF O59 Latin Hypercube Sampling: a space-filling design that draws exactly
  n sample points across any number k of dimensions, in contrast to the full
  factorial design (O58) whose size grows as the product of per-dimension level
  counts. LHS partitions each of the k dimensions into n equal-probability
  strata and places one point per stratum row, so:

      sample-count n k = n            (n evaluations, independent of k)
      strata-per-dimension n k = n    (each dimension is split into n strata)
      total-strata n k = n * k        (n strata across each of k dimensions)

  The defining efficiency property is that the number of objective evaluations
  is n regardless of dimension -- linear, where full factorial is exponential.
  These are exact natural-number counts; the concrete stratum boundaries and the
  Latin-square permutation that assigns points to strata stay an executable
  concern. What is proved here is the sampling-cost arithmetic, reduced by
  reflexivity.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.latin-hypercube`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- sample-count [n k]
  (function/app (function/const* 'latin-hypercube/sample-count []) n k))
(defn- total-strata [n k]
  (function/app (function/const* 'latin-hypercube/total-strata []) n k))

;; Definitions --------------------------------------------------------------

;; sample-count n k = n  (n evaluations, independent of the dimension k)
(def sample-count-spec
  {:name 'latin-hypercube/sample-count :kind :definition :universes []
   :type (function/arrow nat nat nat)
   :value (function/lam [['n nat] ['k nat]] 'n)})

;; strata-per-dimension n k = n  (each dimension is split into n strata)
(def strata-per-dimension-spec
  {:name 'latin-hypercube/strata-per-dimension :kind :definition :universes []
   :type (function/arrow nat nat nat)
   :value (function/lam [['n nat] ['k nat]] 'n)})

;; total-strata n k = n * k
(def total-strata-spec
  {:name 'latin-hypercube/total-strata :kind :definition :universes []
   :type (function/arrow nat nat nat)
   :value (function/lam [['n nat] ['k nat]] (multiply 'n 'k))})

(def definition-specs
  [sample-count-spec strata-per-dimension-spec total-strata-spec])

;; Theorems -----------------------------------------------------------------

;; The defining property: the evaluation count is n for every dimension k.
(def sample-count-is-n-spec
  {:name 'latin-hypercube/sample-count-is-n :universes []
   :type (function/forall [['n nat] ['k nat]]
                          (equality nat (sample-count 'n 'k) 'n))
   :value (function/lam [['n nat] ['k nat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nat (sample-count 'n 'k)))})

;; total-strata unfolds to the product n * k.
(def total-strata-is-product-spec
  {:name 'latin-hypercube/total-strata-is-product :universes []
   :type (function/forall [['n nat] ['k nat]]
                          (equality nat (total-strata 'n 'k)
                                    (multiply 'n 'k)))
   :value (function/lam [['n nat] ['k nat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nat (total-strata 'n 'k)))})

;; Worked counts ------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; A 4-sample LHS in 3 dimensions still makes only 4 objective evaluations...
(def sample-count-4x3-example-spec
  {:name 'latin-hypercube/sample-count-4x3-example :universes []
   :type (equality nat (sample-count (data-nat 4) (data-nat 3)) (data-nat 4))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (sample-count (data-nat 4) (data-nat 3)))})

;; ...while covering 4 x 3 = 12 stratum cells.
(def total-strata-4x3-example-spec
  {:name 'latin-hypercube/total-strata-4x3-example :universes []
   :type (equality nat (total-strata (data-nat 4) (data-nat 3)) (data-nat 12))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (total-strata (data-nat 4) (data-nat 3)))})

(def theorem-specs
  [sample-count-is-n-spec total-strata-is-product-spec
   sample-count-4x3-example-spec total-strata-4x3-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :latin-hypercube (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.latin-hypercube))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
