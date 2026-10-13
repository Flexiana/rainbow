(ns rainbow.math.rational.nnrat.square-zero-test
  "Gate for nnrat/square-zero: m*m ~ 0 -> m ~ 0, axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.square-zero :as nsz2]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nsz2/extend-environment (:environment checkpoint)))))

(deftest nnrat-square-zero-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (nsz2/theorem-ids env)]
    (is (= #{'nnrat/square-zero} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
