(ns rainbow.math.rational.nnrat.farkas-partition-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-partition-list :as plist]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (plist/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest reduced-system-partitions-into-lower-and-upper-lists
  (testing "piece (ii) brick 1: the dependent partition. Given
            reduced-conditions holds at w, there exist a lower-row list and
            an upper-row list (one Product witness) with brick 5b's lower
            fold and brick 4's upper fold both holding at w -- built by
            List.rec resolving each row's lower/upper case. Kernel-checked,
            axiom-free"
    (let [env @checked-environment
          ids (merge (plist/definition-ids env) (plist/theorem-ids env))]
      (is (= #{'nnrat/farkas-partition-list-necessary} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
