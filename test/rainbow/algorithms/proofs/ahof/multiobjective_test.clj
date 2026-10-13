(ns rainbow.algorithms.proofs.ahof.multiobjective-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.multiobjective :as mo]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (mo/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest multiobjective-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (mo/definition-ids env) (mo/theorem-ids env))]
    (is (= #{'mo/dominates 'mo/vega-select 'mo/greedy-nearest 'mo/exchange-step
             'mo/dominates-sound 'mo/vega-keeps-fittest-left 'mo/vega-keeps-fittest-right
             'mo/greedy-nearest-below-left 'mo/greedy-nearest-below-right
             'mo/exchange-accepts 'mo/exchange-rejects}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
