(ns rainbow.ahof-interval-membership-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.interval-arithmetic :as specialization]
            [rainbow.algorithms.proofs.interval-membership :as iteration]
            [rainbow.algorithms.reference.interval-membership :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          specialization/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest interval-membership-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (iteration/definition-ids env) (iteration/theorem-ids env)
                   (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'validation/interval-contains? 'validation/interval-add-endpoint
             'validation/interval-contains-unfold
             'validation/interval-add-endpoint-unfold
             'ahof-v40/lo 'ahof-v40/hi 'ahof-v40/sum-lo-endpoint
             'ahof-v40/sum-hi-endpoint 'ahof-v40/midpoint-inside
             'ahof-v40/below-outside 'ahof-v40/above-outside
             'ahof-v40/sum-lo 'ahof-v40/sum-hi 'ahof-v40/interval-arithmetic}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-interval-membership-matches-worked-instance
  (is (true? (executable/interval-contains? 1/2 3/2 1)))
  (is (false? (executable/interval-contains? 1/2 3/2 1/4)))
  (is (false? (executable/interval-contains? 1/2 3/2 2)))
  (is (= 1 (executable/interval-add-endpoint 1/2 1/2)))
  (is (= 3 (executable/interval-add-endpoint 3/2 3/2))))
