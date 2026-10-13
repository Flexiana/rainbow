(ns rainbow.math.rational.nnrat.farkas-reduce-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (reduce-list/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest both-sides-cross-list-reduces-to-mixed-affine-system
  (testing "recursive-reduction sub-brick (list form): a LIST of both-sides
            cross rows, all holding at v, reduces to a list of affine rows in
            v -- each a lower row (A<=B) or upper row (B<=A) -- by mapping the
            single-row reduction over the list with List.rec. The both-sides
            cross system collapses to a mixed affine-row system in one fewer
            variable. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (reduce-list/definition-ids env)
                     (reduce-list/theorem-ids env))]
      (is (= #{'nnrat/farkas-both-sides-rows-satisfied
               'nnrat/farkas-reduced-conditions
               'nnrat/farkas-reduce-list-necessary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
