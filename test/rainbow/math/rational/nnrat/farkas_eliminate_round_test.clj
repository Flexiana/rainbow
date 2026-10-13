(ns rainbow.math.rational.nnrat.farkas-eliminate-round-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-eliminate-round :as round]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (round/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest one-fourier-motzkin-elimination-round-composes
  (testing "one full FM elimination round, composed: cross-product core
            (bilist) then recursive reduction (reduce-list), with the
            structural bridge (opaque cross conditions -> structured
            both-sides rows) explicit as the `link` hypothesis. Eliminating
            a variable yields a mixed affine-row system in one fewer
            variable. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (round/definition-ids env) (round/theorem-ids env))]
      (is (= #{'nnrat/farkas-eliminate-round}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
