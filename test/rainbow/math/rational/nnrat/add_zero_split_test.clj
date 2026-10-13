(ns rainbow.math.rational.nnrat.add-zero-split-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.add-zero-split :as zs]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (zs/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest add-zero-split-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (zs/definition-ids env) (zs/theorem-ids env))]
    (is (= #{'nat/sum-zero-right 'nat/multiply-succ-zero-left
             'nnrat/add-zero-split-left 'nnrat/add-zero-split-right}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
