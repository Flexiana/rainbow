(ns rainbow.math.rational.nnrat.farkas-partition-row-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-partition-row :as prow]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (prow/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest reduced-row-partitions-to-an-affine-constraint
  (testing "piece (ii) brick 1 core: a reduced disjunction row (lower-exists
            OR upper-exists) becomes the stripped affine constraint
            disjunction (EXISTS D, P<=D*v+Q) OR (EXISTS D, D*v+P<=Q) --
            dropping the difference-witness conjunct. Kernel-checked,
            axiom-free"
    (let [env @checked-environment
          ids (merge (prow/definition-ids env) (prow/theorem-ids env))]
      (is (= #{'nnrat/farkas-partition-row} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
