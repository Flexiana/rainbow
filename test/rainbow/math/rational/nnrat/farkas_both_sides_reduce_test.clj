(ns rainbow.math.rational.nnrat.farkas-both-sides-reduce-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-both-sides-reduce :as reduce]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (reduce/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest both-sides-cross-row-reduces-to-an-affine-row
  (testing "recursive-reduction sub-brick (single-row core): a both-sides
            cross row A*v+P <= B*v+Q reduces, subtraction-free, to an affine
            row in v -- a lower row (EXISTS D, A+D~B and P<=D*v+Q) when A<=B,
            an upper row (EXISTS D, B+D~A and D*v+P<=Q) when B<=A -- by the
            order-totality case-split + difference witness + both-sides
            conversions. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (reduce/definition-ids env) (reduce/theorem-ids env))]
      (is (= #{'nnrat/farkas-both-sides-reduce}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
