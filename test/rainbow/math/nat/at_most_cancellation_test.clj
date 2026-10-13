(ns rainbow.math.nat.at-most-cancellation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.at-most-cancellation :as canc]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (canc/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest nat-at-most-cancellation-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (canc/definition-ids env) (canc/theorem-ids env))]
    (is (= #{'nat/at-most-add-right-cancel 'nat/at-most-add-left-cancel
             'nat/sum-zero-left 'nat/at-most-multiply-right-cancel}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
