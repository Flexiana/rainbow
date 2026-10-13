(ns rainbow.math.rational.nnrat.minmax-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.minmax :as mm]
            [rainbow.math.logic.clamp-range :as cr]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (-> (:environment c)
          mm/extend-environment
          cr/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest general-minmax-bounds-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (mm/definition-ids env) (mm/theorem-ids env))]
    ;; the six universal (forall-quantified) order guarantees plus the two defs
    (is (= #{'minmax/min 'minmax/max
             'minmax/min-lower-left 'minmax/min-lower-right
             'minmax/max-upper-left 'minmax/max-upper-right
             'minmax/at-most-min 'minmax/at-most-max}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))

(deftest clamp-in-range-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (cr/definition-ids env) (cr/theorem-ids env))]
    (is (= #{'clamp/clamp 'clamp/clamp-at-most-hi 'clamp/lo-at-most-clamp}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
