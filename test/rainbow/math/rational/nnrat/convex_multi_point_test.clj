(ns rainbow.math.rational.nnrat.convex-multi-point-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.convex-multi-point :as convex-multi-point]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (convex-multi-point/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest nnrat-multi-point-convex-bracket-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (convex-multi-point/definition-ids env)
                   (convex-multi-point/theorem-ids env))]
    (is (= #{'nnrat/weighted-combo-at-least
             'nnrat/weighted-combo-at-most}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
