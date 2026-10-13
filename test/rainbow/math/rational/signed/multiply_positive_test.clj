(ns rainbow.math.rational.signed.multiply-positive-test
  "Cold gate: 0 < a -> 0 < b -> 0 < a*b, kernel-checked and axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply-positive :as m]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (m/extend-environment (:environment checkpoint)))))

(deftest multiply-positive-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (m/theorem-ids env)]
    (is (= #{'signed/multiply-positive} (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
