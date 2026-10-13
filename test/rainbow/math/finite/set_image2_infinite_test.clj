(ns rainbow.math.finite.set-image2-infinite-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-image2-infinite :as image2]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def transfer-targets
  #{"Set.Infinite.image2_left" "Set.Infinite.image2_right"
    "Set.infinite_image2" "Set.infinite_prod"})

(defn fixture []
  (let [checkpoint
        (checkpoint/load-checkpoint "artifacts/day73/checkpoint.edn.gz")
        checked (image2/extend-environment (:environment checkpoint))]
    {:checkpoint checkpoint :environment checked
     :ids (image2/theorem-ids checked)}))

(deftest binary-image-support-is-kernel-checked-and-exactly-classical
  (let [{:keys [checkpoint environment ids]} (fixture)
        excluded-middle-id
        (environment/resolve-id environment 'logic/excluded-middle)]
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
        (is (= #{excluded-middle-id} (kernel/axioms environment id))
            (str alias))))))

(deftest binary-image-support-transfers-to-four-residual-statements
  (let [{:keys [checkpoint environment ids]} (fixture)
        index (reuse/build-index environment {:include-ids (vals ids)})
        excluded-middle-id
        (environment/resolve-id environment 'logic/excluded-middle)
        targets
        (filterv #(contains? transfer-targets (:foreign/name %))
                 (:remaining-targets checkpoint))]
    (is (= 4 (count targets)))
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
        (is (= #{excluded-middle-id}
               (get-in result [:proof :proof/axioms]))
            (:foreign/name target))
        (is (= :checked (get-in result [:kernel :status]))
            (:foreign/name target))))))
