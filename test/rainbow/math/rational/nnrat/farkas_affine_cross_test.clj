(ns rainbow.math.rational.nnrat.farkas-affine-cross-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-affine-cross :as cross]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cross/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest affine-cross-necessary-holds
  (testing "brick 5c full of the general LP FM encoding: the coefficient
            affine cross-elimination crux -- from w_lo <= a_lo*v + s_lo and
            a_hi*v + s_hi <= b_hi, eliminating v yields
            w_lo*a_hi + s_hi*a_lo <= b_hi*a_lo + s_lo*a_hi (necessary
            direction), by cross-scaling + distributing + product alignment
            down to the additive core. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cross/definition-ids env) (cross/theorem-ids env))]
      (is (= #{'nnrat/farkas-affine-cross-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
