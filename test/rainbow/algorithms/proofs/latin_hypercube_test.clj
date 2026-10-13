(ns rainbow.algorithms.proofs.latin-hypercube-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.latin-hypercube :as lhs]
            [rainbow.algorithms.reference.latin-hypercube :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lhs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest latin-hypercube-counts-are-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lhs/definition-ids checked-environment)
        theorems (lhs/theorem-ids checked-environment)]
    (is (= #{'latin-hypercube/sample-count
             'latin-hypercube/strata-per-dimension
             'latin-hypercube/total-strata}
           (set (keys definitions))))
    (is (= #{'latin-hypercube/sample-count-is-n
             'latin-hypercube/total-strata-is-product
             'latin-hypercube/sample-count-4x3-example
             'latin-hypercube/total-strata-4x3-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-latin-hypercube-matches-the-counts
  (is (= 4 (executable/sample-count 4 3)))
  (is (= 12 (executable/total-strata 4 3)))
  ;; A concrete LHS: 3 points in 2 dimensions, identity permutation on dim 0 and
  ;; a shifted permutation on dim 1 -- each stratum index used once per axis.
  (let [design (executable/design 3 2 {0 [0 1 2] 1 [2 0 1]})]
    (is (= 3 (count design)))
    (is (every? #(= 2 (count %)) design))
    ;; Latin property: every stratum index 0..2 appears exactly once per column.
    (is (= #{0 1 2} (set (map first design))))
    (is (= #{0 1 2} (set (map second design))))))
