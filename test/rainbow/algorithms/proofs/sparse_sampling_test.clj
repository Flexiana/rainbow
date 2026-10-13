(ns rainbow.algorithms.proofs.sparse-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.power :as nat-power]
            [rainbow.algorithms.proofs.sparse-sampling :as sparse-sampling]
            [rainbow.algorithms.reference.sparse-sampling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-power/extend-environment
          sparse-sampling/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest sparse-sampling-count-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sparse-sampling/definition-ids checked-environment)
        theorems (sparse-sampling/theorem-ids checked-environment)]
    (is (= #{'sparse-sampling/node-count} (set (keys definitions))))
    (is (= #{'sparse-sampling/node-count-is-power
             'sparse-sampling/horizon-zero-single-node
             'sparse-sampling/node-count-example
             'sparse-sampling/node-count-deep-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-sparse-sampling-matches-the-count
  (is (= 36 (executable/node-count 2 3 2)))
  (is (= 64 (executable/node-count 2 2 3)))
  (is (= 1 (executable/node-count 5 4 0)))
  ;; The count is the same whatever the state-space size.
  (is (executable/independent-of-states? 2 3 2 1000 1000000)))
