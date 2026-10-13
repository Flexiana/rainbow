(ns rainbow.math.rational.signed.square-nonzero-test
  "Gate for signed square nonzero/positive: d≁0 -> d*d≁0 and d≁0 -> 0 < d*d, axiom-free.
  Embeds the nnrat AM-GM discriminant via the signed pair unfold; this is x!=y -> 0 < (x-y)^2."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.square-nonzero :as ssn]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (ssn/extend-environment (:environment checkpoint)))))

(deftest signed-square-nonzero-and-positive-are-checked-and-axiom-free
  (let [env @checked-environment
        ids (ssn/theorem-ids env)]
    (is (= #{'signed/square-nonzero 'signed/square-positive} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
