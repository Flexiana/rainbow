(ns rainbow.algorithms.proofs.robustness-objective-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.robustness-objective :as ahof-v13]
            [rainbow.algorithms.proofs.robustness-objective :as iteration]
            [rainbow.math.rational.signed.order :as signed-order]
            [rainbow.algorithms.reference.robustness-objective :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/v4-cross-validation/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "V4 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          signed-order/extend-environment
          iteration/extend-environment
          ahof-v13/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest robustness-objective-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'validation/falsification-objective} (set (keys definitions))))
    (is (= #{'validation/falsification-objective-unfold
             'validation/falsification-objective-involution}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-v13-robustness-objective-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-v13/theorem-ids checked-environment)]
    (is (= #{'ahof-v13/satisfying-objective-is-negative-two
             'ahof-v13/violating-objective-is-one
             'ahof-v13/robustness-objective}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-robustness-objective-flips-the-sign
  ;; The falsification objective negates the robustness: a satisfying trajectory
  ;; (robustness 2) scores -2, a violating one (robustness -1) scores 1, so
  ;; maximizing the objective favours the violating trajectory.
  (is (= -2 (executable/falsification-objective 2)))
  (is (= 1 (executable/falsification-objective -1)))
  (is (> (executable/falsification-objective -1)
         (executable/falsification-objective 2)))
  ;; Negating twice recovers the robustness.
  (is (= 3 (executable/falsification-objective
            (executable/falsification-objective 3)))))
