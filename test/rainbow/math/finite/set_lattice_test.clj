(ns rainbow.math.finite.set-lattice-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-lattice :as lattice]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def transfer-targets
  #{"Set.Infinite.inter_of_finite_diff"
    "TopologicalSpace.cofinite._proof_1"
    "TopologicalSpace.cofinite._proof_2"
    "TopologicalSpace.cofinite._proof_3"})

(defn fixture []
  (let [checkpoint
        (checkpoint/load-checkpoint "artifacts/day72/checkpoint.edn.gz")
        checked (lattice/extend-environment (:environment checkpoint))]
    {:checkpoint checkpoint :environment checked
     :ids (lattice/theorem-ids checked)}))

(deftest lattice-support-has-explicit-minimal-axiom-profiles
  (let [{:keys [checkpoint environment ids]} (fixture)
        excluded-middle-id
        (environment/resolve-id environment 'logic/excluded-middle)
        expected
        {'set/finite-complement-universal #{}
         'set/finite-complement-intersection #{excluded-middle-id}
         'set/finite-complement-supremum #{}
         'set/infinite-intersection-of-finite-difference
         #{excluded-middle-id}}]
    (is (= :replayed (:status checkpoint)))
    (is (= 4 (count ids)))
    (doseq [[alias id] ids]
      (let [declaration (environment/declaration environment id)
            replay
            (kernel/check environment
                          (:rainbow/value declaration)
                          (:rainbow/type declaration)
                          (set (:rainbow/universes declaration)))]
        (is (= :checked (:status replay)) (str alias))
        (is (= (get expected alias) (kernel/axioms environment id))
            (str alias))))))

(deftest lattice-support-transfers-exactly-across-all-partitions
  (let [{:keys [checkpoint environment ids]} (fixture)
        index (reuse/build-index environment {:include-ids (vals ids)})
        excluded-middle-id
        (environment/resolve-id environment 'logic/excluded-middle)
        targets
        (filterv #(contains? transfer-targets (:foreign/name %))
                 (:remaining-targets checkpoint))]
    (is (= 4 (count targets)))
    (is (= #{:development :held-out :transfer}
           (set (map #(get (:remaining-partitions checkpoint)
                           (:foreign/name %))
                     targets))))
    (doseq [target targets]
      (is (= :blocked
             (get-in checkpoint
                     [:latest-outcomes (:foreign/name target) :status])))
      (let [result
            (search/prove
             (:state (proof/start environment (:type target)
                                  {:universes (:universes target)}))
             {:states 2 :wall-ms 10000 :reuse-index index
              :reuse-policy {:allowed-axioms #{excluded-middle-id}}})]
        (is (= :proved (:status result)) (:foreign/name target))
        (is (= 1 (get-in result [:telemetry :reuse-successes]))
            (:foreign/name target))
        (is (= :checked (get-in result [:kernel :status]))
            (:foreign/name target))))))
