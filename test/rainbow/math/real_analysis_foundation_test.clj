(ns rainbow.math.real-analysis-foundation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.real-analysis-foundation :as ra]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (ra/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest real-analysis-foundation-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (ra/definition-ids env) (ra/theorem-ids env))]
    (is (= #{'analysis/nondecreasing 'analysis/bounded-above 'analysis/constant
             'analysis/constant-nondecreasing 'analysis/constant-bounded-by-self}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
