(ns rainbow.math.rational.signed.square-strict-convex-test
  "Cold gate: strict convexity of the square (x != y, positive weights -> strict inequality),
  plus the from-nnrat-nonzero bridge and the strict-convex-on predicate. Axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.square-strict-convex :as m]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (m/extend-environment (:environment checkpoint)))))

(deftest strict-convexity-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (m/theorem-ids env)]
    (is (= #{'signed/from-nnrat-nonzero 'signed/strict-convex-on 'signed/square-strict-convex}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
