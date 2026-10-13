(ns rainbow.history.finite-carriers-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finite-carriers :as finite-carriers]))

(def expected-names
  #{"fintypeOfNotInfinite._proof_1" "Set.infinite_univ_iff"
    "Set.finite_univ_iff" "Finite.of_finite_univ" "infinite_prod"})

(deftest finite-carrier-report-is-content-addressed-and-held-out-validated
  (let [result (finite-carriers/load-report finite-carriers/report-path)
        report (edn/read-string (slurp finite-carriers/report-path))]
    (is (= :replayed (:status result)))
    (is (= "sha256:60efbff921816a9ea0992ecbe7041475e71b6ab8063273a8459f14f9e2b2faa6"
           (:report/id result)))
    (is (= false (get-in report [:claim-boundaries
                                 :development-only-proof-gain?])))
    (is (= 1 (get-in report [:claim-boundaries :validation-proof-gain])))
    (is (= {:blocked 1 :proved 1}
           (get-in report [:experiment :validation :statuses])))
    (is (= true
           (get-in report [:experiment :validation
                           :representation-promoted-globally?])))))

(deftest finite-carrier-checkpoint-replays-five-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finite-carriers/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        product-mapping
        (first (filter #(= "infinite_prod" (:foreign/name %)) mappings))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:5f18daf66070546d34537e77279baf5390d154832b4899e671302d81e36cdf4d"
           (:checkpoint/id checkpoint)))
    (is (= 1180 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 5 (count (set (map :proof/id mappings)))))
    (is (= 1 (count (:axioms product-mapping))))))
