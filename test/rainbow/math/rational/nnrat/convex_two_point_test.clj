(ns rainbow.math.rational.nnrat.convex-two-point-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.convex-two-point :as convex-two-point]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (convex-two-point/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest nnrat-two-point-convex-bracket-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (convex-two-point/definition-ids env)
                   (convex-two-point/theorem-ids env))]
    (is (= #{'nnrat/two-point-at-least-scaled-min
             'nnrat/two-point-at-most-scaled-max}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
