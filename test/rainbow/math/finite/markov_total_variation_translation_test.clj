(ns rainbow.math.finite.markov-total-variation-translation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-total-variation-translation :as translation]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (translation/extend-environment (:environment checkpoint)))))

(deftest common-mass-cancels-from-both-finite-distances
  (let [env @checked-environment ids (translation/theorem-ids env)]
    (is (= 2 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u})))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
