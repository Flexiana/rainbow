(ns rainbow.algorithms.proofs.ahof.counting-sort
  "AHoF Counting Sort: a stable, NON-comparison, O(n + k) sort for integer keys in
  a small range [0, k). Count how many items have each key, then take the
  CUMULATIVE counts (a prefix sum) to get each key's ending offset in the output,
  and place items from the end for stability. The cumulative counts are exactly the
  proved prefix-sum scan applied to the count histogram:

      cumulative-counts = cumulative-sum counts.

  Proved native and axiom-free: the cumulative counts reuse the proved
  prefix-sum/cumulative-sum fold (a worked histogram [2,1,3] -> offsets [2,3,6]),
  and its length-preservation and prefix-sum correctness are already proved
  in general (scan-length, scan-correctness). The histogram build and the stable
  placement are executable; what is proved is that the placement offsets are the
  prefix sum of the counts.

  Requires prefix-sum/cumulative-sum, algebra/nat-add, data/cons/nil (the
  prefix-sum module composed here plus the D63 checkpoint).

  Scope (measured by the kernel): this module has 1 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.counting-sort`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.prefix-sum :as prefix-sum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def list-nat
  (function/app (function/const* 'data/List [type-level]) nat))

(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))
(def nil-nat
  (function/app (function/const* 'data/nil [type-level]) nat))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cumulative-sum [xs]
  (function/app (function/const* 'prefix-sum/cumulative-sum []) xs))
(defn- cumulative-counts [counts]
  (function/app (function/const* 'counting-sort/cumulative-counts []) counts))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- nat-list [& elements]
  (reduce (fn [tail element] (cons-nat element tail)) nil-nat (reverse elements)))

;; Definitions --------------------------------------------------------------

;; cumulative-counts counts = cumulative-sum counts (the placement offsets)
(def cumulative-counts-spec
  {:name 'counting-sort/cumulative-counts :kind :definition :universes []
   :type (function/arrow list-nat list-nat)
   :value (function/lam [['counts list-nat]] (cumulative-sum 'counts))})

(def definition-specs [cumulative-counts-spec])

;; Theorems -----------------------------------------------------------------

;; Histogram [2,1,3] (two 0s, one 1, three 2s) gives ending offsets [2,3,6].
(def offsets-example-spec
  {:name 'counting-sort/offsets-example :universes []
   :type (equality list-nat
                   (cumulative-counts (nat-list (data-nat 2) (data-nat 1)
                                                (data-nat 3)))
                   (nat-list (data-nat 2) (data-nat 3) (data-nat 6)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        list-nat
                        (cumulative-counts (nat-list (data-nat 2) (data-nat 1)
                                                     (data-nat 3))))})

;; The offsets are, by definition, the prefix-sum scan of the counts (reusing the
;; proved scan): cumulative-counts xs = cumulative-sum xs for all count vectors.
(def offsets-are-prefix-sum-spec
  {:name 'counting-sort/offsets-are-prefix-sum :universes []
   :type (function/forall
          [['counts list-nat]]
          (equality list-nat (cumulative-counts 'counts)
                    (cumulative-sum 'counts)))
   :value (function/lam
           [['counts list-nat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         list-nat (cumulative-counts 'counts)))})

(def theorem-specs [offsets-example-spec offsets-are-prefix-sum-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      prefix-sum/extend-environment
      (support/extend-with :ahof-counting-sort
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
