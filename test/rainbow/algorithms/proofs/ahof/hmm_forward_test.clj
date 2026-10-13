(ns rainbow.algorithms.proofs.ahof.hmm-forward-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.hmm-forward :as hmm]
            [rainbow.algorithms.reference.hmm-forward :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          hmm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hmm-forward-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hmm/definition-ids checked-environment)
        theorems (hmm/theorem-ids checked-environment)]
    (is (= #{'hmm-forward/alpha-step} (set (keys definitions))))
    (is (= #{'hmm-forward/alpha-step-example 'hmm-forward/certain-predecessor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hmm-forward
  (is (= 1/2 (executable/alpha-step 1/2 1/2 1/2 1/2 1)))
  (is (= 1 (executable/alpha-step 1 1 0 0 1)))
  ;; 2-state HMM, obs [0], init 1/2 each, emit 1: likelihood 1
  (is (= 1 (executable/likelihood 2 [0] (fn [_] 1/2) (fn [_ _] 1/2)
                                  (fn [_ _] 1)))))
