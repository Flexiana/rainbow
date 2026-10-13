(ns rainbow.algorithms.proofs.ahof.bucket-sort
  "AHoF Bucket Sort: sort values drawn from a uniform range in EXPECTED linear time
  by distributing them into ordered buckets by value, sorting each bucket
  (with any comparison sort), and CONCATENATING the buckets in order. It beats
  comparison sorts' n log n bound in expectation when the input is uniform (few
  items per bucket). Correctness rests on emitting buckets in increasing index so
  every value of a lower bucket precedes every value of a higher one:

      bucket-precedes? bucket-a bucket-b = decide (bucket-a <= bucket-b)

  over exact-rational (integer) bucket indices. Defined: the bucket-order test.
  Proved native and axiom-free, as worked instances: bucket 1 precedes bucket 4,
  bucket 4 does not precede bucket 1, and the worked certificate 1 <= 4 (native
  nnrat/at-most). That the concatenation is globally sorted, and the expected
  linear running time, are classical and not proved here. The value-to-bucket
  distribution and per-bucket sort are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bucket-sort`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- bucket-precedes? [bucket-a bucket-b]
  (function/app (function/const* 'bucket-sort/bucket-precedes? []) bucket-a bucket-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; bucket-precedes? bucket-a bucket-b = decide (bucket-a <= bucket-b)
(def bucket-precedes-spec
  {:name 'bucket-sort/bucket-precedes? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['bucket-a nnrat] ['bucket-b nnrat]]
                        (decide-at-most 'bucket-a 'bucket-b))})

(def definition-specs [bucket-precedes-spec])

;; Theorems -----------------------------------------------------------------

;; Bucket 1 is emitted before bucket 4 (its values are all smaller).
(def lower-bucket-first-spec
  {:name 'bucket-sort/lower-bucket-first :universes []
   :type (equality bool (bucket-precedes? (whole 1) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (bucket-precedes? (whole 1) (whole 4)))})

;; Worked certificate 1 <= 4.
(def preceding-bucket-index-at-most-spec
  {:name 'bucket-sort/preceding-bucket-index-at-most :universes []
   :type (nnrat-at-most (whole 1) (whole 4))
   :value (at-most-proof (whole 1) (whole 4))})

;; Bucket 4 does not come before bucket 1 (it is emitted later).
(def higher-bucket-later-spec
  {:name 'bucket-sort/higher-bucket-later :universes []
   :type (equality bool (bucket-precedes? (whole 4) (whole 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (bucket-precedes? (whole 4) (whole 1)))})

(def theorem-specs
  [lower-bucket-first-spec preceding-bucket-index-at-most-spec
   higher-bucket-later-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bucket-sort
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
