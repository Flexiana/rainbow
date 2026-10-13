(ns rainbow.math.rational.nnrat.square-positive-test
  "Gate for nnrat/square-positive: positive k -> positive (k*k), axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.square-positive :as nsp]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nsp/extend-environment (:environment checkpoint)))))

(deftest nnrat-square-positive-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (nsp/theorem-ids env)]
    (is (= #{'nnrat/square-positive} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
