(ns rainbow.math.rational.nnrat.farkas-cross-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-list :as cross-list]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cross-list/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest cross-list-necessary-holds
  (testing "brick 5d-i of the general LP FM encoding: the cross-product of
            one affine lower row against a LIST of affine upper rows. Any v
            satisfying the lower row and every upper row yields every upper
            row's cross condition (brick 5c mapped over the list by
            List.rec) -- the reduced system for the two-variable objective
            boundary. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cross-list/definition-ids env)
                     (cross-list/theorem-ids env))]
      (is (= #{'nnrat/farkas-cross-list-conditions
               'nnrat/farkas-cross-list-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
