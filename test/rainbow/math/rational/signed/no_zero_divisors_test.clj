(ns rainbow.math.rational.signed.no-zero-divisors-test
  "Gate for the nonzero base facts toward strict convexity: nnrat and signed 1 !~ 0, and the
  first strict inequality 0 < 1, all kernel-checked and axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.no-zero-divisors :as nzd]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nzd/extend-environment (:environment checkpoint)))))

(deftest nonzero-facts-are-checked-and-axiom-free
  (let [env @checked-environment
        ids (nzd/theorem-ids env)]
    (is (= #{'nnrat/one-not-equivalent-zero 'signed/one-not-equivalent-zero
             'signed/zero-less-than-one}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
