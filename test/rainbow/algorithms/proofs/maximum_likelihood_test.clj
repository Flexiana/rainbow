(ns rainbow.algorithms.proofs.maximum-likelihood-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.maximum-likelihood :as ahof-d10]
            [rainbow.algorithms.proofs.maximum-likelihood :as iteration]
            [rainbow.algorithms.reference.maximum-likelihood :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d18-decision-network/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D18 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d10/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest maximum-likelihood-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'estimation/log-likelihood-total 'estimation/mle-prefers}
           (set (keys definitions))))
    (is (= #{'estimation/log-likelihood-total-unfold
             'estimation/mle-prefers-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d10-maximum-likelihood-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d10/theorem-ids checked-environment)]
    (is (= #{'ahof-d10/model-a-total-is-three-halves
             'ahof-d10/model-b-total-is-one-half
             'ahof-d10/mle-prefers-model-a
             'ahof-d10/maximum-likelihood}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-maximum-likelihood-prefers-higher-total
  ;; Model A scores 3/4 and 3/4 (total 3/2); model B scores 1/4 and 1/4 (total
  ;; 1/2). Maximum likelihood prefers model A.
  (is (= 3/2 (executable/log-likelihood-total [3/4 3/4])))
  (is (= 1/2 (executable/log-likelihood-total [1/4 1/4])))
  (is (true? (executable/mle-prefers? 3/2 1/2)))
  (is (= :model-a (executable/estimate [3/4 3/4] [1/4 1/4])))
  (is (= :model-b (executable/estimate [1/4 1/4] [3/4 3/4]))))
