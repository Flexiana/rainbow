(ns rainbow.math.rational.signed.recovery-laws-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.recovery-laws :as recovery]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (recovery/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest signed-recovery-laws-are-native-and-axiom-free
  (testing "two general signed laws the corpus lacked, promoted from the
            Gauss-Seidel proof to a core module: the (a-b)+b recovery law
            and reciprocal-scale cancellation"
    (let [env @checked-environment
          ids (merge (recovery/definition-ids env) (recovery/theorem-ids env))]
      (is (= #{'signed/subtract-then-add 'signed/reciprocal-scale-cancel}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
