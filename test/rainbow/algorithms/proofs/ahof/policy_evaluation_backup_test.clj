(ns rainbow.algorithms.proofs.ahof.policy-evaluation-backup-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.policy-evaluation-backup :as pe]
            [rainbow.algorithms.reference.policy-evaluation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pe/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest policy-evaluation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pe/definition-ids checked-environment)
        theorems (pe/theorem-ids checked-environment)]
    (is (= #{'policy-eval/backup} (set (keys definitions))))
    (is (= #{'policy-eval/backup-example 'policy-eval/myopic-at-zero-discount}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-policy-evaluation
  (is (= 5/2 (executable/bellman-eval 1 1/2 3)))
  (is (= 4 (executable/bellman-eval 4 0 9)))
  ;; fixed point of V = 1 + 1/2 V is 2; iterating from 0 approaches it
  (is (= 7/4 (executable/evaluate 1 1/2 3 0))))
