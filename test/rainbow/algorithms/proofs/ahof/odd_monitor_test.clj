(ns rainbow.algorithms.proofs.ahof.odd-monitor-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.odd-monitor :as specialization]
            [rainbow.algorithms.proofs.odd-monitor :as iteration]
            [rainbow.algorithms.reference.odd-monitor :as executable]))

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

(deftest odd-monitor-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (iteration/definition-ids env) (iteration/theorem-ids env)
                   (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'monitor/in-odd? 'monitor/in-odd-unfold
             'ahof-v59/lo1 'ahof-v59/hi1 'ahof-v59/lo2 'ahof-v59/hi2
             'ahof-v59/inside-accepted 'ahof-v59/dim2-above-rejected
             'ahof-v59/dim1-above-rejected 'ahof-v59/odd-monitor}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-odd-monitor-matches-worked-instance
  ;; box [0,1] x [0,2]
  (is (true? (executable/in-odd? 0 1 1/2 0 2 1)))
  (is (false? (executable/in-odd? 0 1 1/2 0 2 3)))
  (is (false? (executable/in-odd? 0 1 2 0 2 1))))
