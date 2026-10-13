(ns rainbow.math.rational.nnrat.farkas-cross-bilist-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-bilist :as bilist]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (bilist/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest bilist-cross-product-necessary-holds
  (testing "brick 6 cross-product core of the general LP FM encoding: the
            cross-product over BOTH row lists. Any v satisfying every affine
            lower row and every affine upper row yields, for each lower row,
            that lower's whole cross-condition list (5d-i mapped over the
            lower list) -- the general elimination step the n-variable
            induction folds. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (bilist/definition-ids env) (bilist/theorem-ids env))]
      (is (= #{'nnrat/farkas-lowers-satisfied
               'nnrat/farkas-cross-bilist-conditions
               'nnrat/farkas-cross-bilist-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
