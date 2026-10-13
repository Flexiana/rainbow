(ns rainbow.math.rational.nnrat.farkas-bridge-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-bridge-list :as bridge-list]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (bridge-list/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest bridge-maps-over-the-structured-cross-row-list
  (testing "piece 1 bridge-mapping: given the cross condition holds at w for
            every structured cross row, the corresponding both-sides row
            holds for every row, by mapping the single-row bridge over the
            list. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (bridge-list/definition-ids env)
                     (bridge-list/theorem-ids env))]
      (is (= #{'nnrat/farkas-bridge-cross-holds
               'nnrat/farkas-bridge-both-sides-hold
               'nnrat/farkas-bridge-list-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
