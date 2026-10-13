(ns rainbow.algorithms.proofs.trust-region-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.trust-region :as ahof-o16]
            [rainbow.algorithms.proofs.trust-region :as iteration]
            [rainbow.algorithms.reference.trust-region :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o31-levenberg-marquardt/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O31 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o16/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest trust-region-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'decision/reduction-ratio 'decision/trust-accept
             'decision/trust-region-update}
           (set (keys definitions))))
    (is (= #{'decision/reduction-ratio-unfold 'decision/trust-accept-unfold
             'decision/trust-region-update-accepts
             'decision/trust-region-update-rejects}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o16-trust-region-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o16/theorem-ids checked-environment)]
    (is (= #{'ahof-o16/accept-decision-is-true
             'ahof-o16/reject-decision-is-false
             'ahof-o16/accepted-step-is-candidate
             'ahof-o16/rejected-step-is-current
             'ahof-o16/trust-region}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-trust-region-accepts-and-rejects
  ;; threshold 1/2, candidate 0, current 2. Matched prediction (ratio 1) clears
  ;; the threshold, so the step is accepted to the candidate 0. Over-prediction
  ;; (ratio 1/4) fails, so the step is rejected, keeping the current 2.
  (is (= 1 (executable/reduction-ratio 1 1)))
  (is (= 1/4 (executable/reduction-ratio 1 4)))
  (is (true? (executable/trust-accept? 1/2 1)))
  (is (false? (executable/trust-accept? 1/2 1/4)))
  (is (= 0 (executable/step 1/2 1 1 0 2)))
  (is (= 2 (executable/step 1/2 1 4 0 2))))
