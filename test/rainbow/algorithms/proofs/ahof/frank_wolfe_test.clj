(ns rainbow.algorithms.proofs.ahof.frank-wolfe-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.frank-wolfe :as fw]
            [rainbow.algorithms.reference.frank-wolfe :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          fw/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest frank-wolfe-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (fw/definition-ids checked-environment)
        theorems (fw/theorem-ids checked-environment)]
    (is (= #{'frank-wolfe/step} (set (keys definitions))))
    (is (= #{'frank-wolfe/half-step 'frank-wolfe/full-step-to-vertex
             'frank-wolfe/null-step-stays}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-frank-wolfe-step
  (is (= 1 (executable/fw-step 2 0 1/2 1/2)))
  (is (= 7 (executable/fw-step 2 7 0 1)))
  (is (= 2 (executable/fw-step 2 7 1 0)))
  ;; gamma=1/2 from x=4 toward s=0: (1/2)*4 = 2
  (is (= 2 (executable/fw-step-gamma 4 0 1/2))))
