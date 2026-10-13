(ns rainbow.math.rational.nnrat.farkas-reduced-vector-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-reduced-vector :as rv]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (rv/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest cross-condition-becomes-a-both-sides-vector-constraint
  (testing "unified representation brick 2 assembly: the cross condition
            w_lo*a_hi + eval(U_tail)*a_lo <= b_hi*a_lo + eval(L_tail)*a_hi
            rewrites (via the scale lemma both sides) to
            w_lo*a_hi + eval(scale a_lo U_tail) <= b_hi*a_lo + eval(scale a_hi L_tail)
            -- a both-sides linear constraint over the tail with transformed
            coefficient vectors. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (rv/definition-ids env) (rv/theorem-ids env))]
      (is (= #{'nnrat/farkas-reduced-vector} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
