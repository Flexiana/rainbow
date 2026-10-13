(ns rainbow.math.rational.nnrat.farkas-form-scale-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-form-scale :as scale]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (scale/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest scaling-a-linear-form-scales-its-coefficient-vector
  (testing "unified representation brick 2 core: eval(pairs)*c ~
            eval(scale-right c pairs), where scale-right multiplies each
            coefficient by c. The cross's product terms are linear forms
            over the same tail variables with scaled coefficient vectors.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (scale/definition-ids env) (scale/theorem-ids env))]
      (is (= #{'nnrat/farkas-scale-right 'nnrat/farkas-form-scale-right}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
