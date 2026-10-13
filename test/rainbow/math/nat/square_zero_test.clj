(ns rainbow.math.nat.square-zero-test
  "Gate for nat/square-zero-implies-zero: a*a = 0 -> a = 0, axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.square-zero :as nsz]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nsz/extend-environment (:environment checkpoint)))))

(deftest nat-square-zero-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (nsz/theorem-ids env)]
    (is (= #{'nat/square-zero-implies-zero} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
