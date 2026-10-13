(ns rainbow.math.rational.nnrat.farkas-both-sides-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-both-sides :as both-sides]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (both-sides/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest both-sides-row-converts-to-affine-lower-and-upper
  (testing "brick 5d-ii of the general LP FM encoding: a both-sides row
            A*v + P <= B*v + Q converts subtraction-free to an affine row in
            v -- to a LOWER row P <= D*v + Q when A <= B (witness A+D~B), and
            to an UPPER row D*v + P <= Q when B <= A (witness B+D~A), by
            cancelling the common variable term. Both directions, so the
            recursive reduction can case-split each cross condition.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (both-sides/definition-ids env)
                     (both-sides/theorem-ids env))]
      (is (= #{'nnrat/farkas-both-sides-to-lower
               'nnrat/farkas-both-sides-to-upper}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
