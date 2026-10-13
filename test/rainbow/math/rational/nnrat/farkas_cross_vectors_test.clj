(ns rainbow.math.rational.nnrat.farkas-cross-vectors-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-vectors :as cv]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cv/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest crossing-two-coefficient-vector-constraints-eliminates-a-variable
  (testing "unified representation brick 3 core: crossing a lower and an
            upper coefficient-vector constraint on the shared head variable
            x1 yields the reduced both-sides vector constraint over the tail
            -- composing head-split, the affine cross crux, and reduced-vector.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cv/definition-ids env) (cv/theorem-ids env))]
      (is (= #{'nnrat/farkas-cross-vectors} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
