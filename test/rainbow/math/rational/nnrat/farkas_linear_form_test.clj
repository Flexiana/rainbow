(ns rainbow.math.rational.nnrat.farkas-linear-form-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-linear-form :as lf]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lf/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest coefficient-vector-representation-and-head-split
  (testing "unified representation brick 1: nnrat/linear-form evaluates a
            coefficient-vector constraint (sum c_i*x_i); the upper/lower
            head-split lemmas expose each row as head_coeff*head_var + block
            (block = eval of the tail), presenting a vector row as the
            structured affine row the round consumes. Kernel-checked,
            axiom-free"
    (let [env @checked-environment
          ids (merge (lf/definition-ids env) (lf/theorem-ids env))]
      (is (= #{'nnrat/linear-form
               'nnrat/linear-form-upper-split
               'nnrat/linear-form-lower-split}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
