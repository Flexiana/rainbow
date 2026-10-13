(ns rainbow.algorithms.proofs.composite-metric-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.composite-metric :as ahof-v5]
            [rainbow.algorithms.proofs.composite-metric :as iteration]
            [rainbow.algorithms.reference.composite-metric :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/v13-robustness-objective/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "V13 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-v5/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest composite-metric-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'validation/composite-metric} (set (keys definitions))))
    (is (= #{'validation/composite-metric-unfold} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-v5-composite-metric-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-v5/theorem-ids checked-environment)]
    (is (= #{'ahof-v5/balanced-is-one-half
             'ahof-v5/accuracy-weighted-is-three-quarters
             'ahof-v5/composite-metric}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-composite-metric-weights-the-atomic-metrics
  ;; Accuracy 3/4 and precision 1/4. Balanced weights average them to 1/2;
  ;; accuracy-only weights (1, 0) return the accuracy 3/4 -- the weights change
  ;; the aggregate.
  (is (= 1/2 (executable/composite-metric 1/2 3/4 1/2 1/4)))
  (is (= 3/4 (executable/composite-metric 1 3/4 0 1/4)))
  (is (= 1/4 (executable/composite-metric 0 3/4 1 1/4)))
  (is (not= (executable/composite-metric 1/2 3/4 1/2 1/4)
            (executable/composite-metric 1 3/4 0 1/4))))
