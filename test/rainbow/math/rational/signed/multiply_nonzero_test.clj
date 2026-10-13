(ns rainbow.math.rational.signed.multiply-nonzero-test
  "Cold gate: kernel-checked, axiom-free membership of the general no-zero-divisors chain."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply-nonzero :as m]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (m/extend-environment (:environment checkpoint)))))

(deftest theorems-are-checked-and-axiom-free
  (let [env @checked-environment
        ids (m/theorem-ids env)]
    (is (= #{'signed/multiply-zero-split 'signed/multiply-nonzero} (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str nm))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
