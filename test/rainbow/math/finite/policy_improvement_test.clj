(ns rainbow.math.finite.policy-improvement-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.policy-improvement :as pimp]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d20-policy-evaluation/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D20 checkpoint rejected" {:checkpoint checkpoint})))
      (pimp/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest improve-dominates-current-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (pimp/definition-ids env) (pimp/theorem-ids env))]
    (is (= #{'policy/nnrat-improve-dominates-current} (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
