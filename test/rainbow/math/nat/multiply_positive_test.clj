(ns rainbow.math.nat.multiply-positive-test
  "Gate for nat/multiply-positive: 0 < a -> 0 < b -> 0 < a*b (strict-below), axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.multiply-positive :as nmp]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nmp/extend-environment (:environment checkpoint)))))

(deftest nat-multiply-positive-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (nmp/theorem-ids env)]
    (is (= #{'nat/multiply-positive} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
