(ns rainbow.math.rational.nnrat.farkas-cross-vectors-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-list :as cvl]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cvl/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest one-lower-crosses-a-list-of-upper-vector-constraints
  (testing "brick 3 per-pair fold: a lower coefficient-vector constraint
            crossed against a LIST of upper coefficient-vector constraints,
            all holding at x1, yields every pairwise reduced both-sides vector
            constraint -- cross-vectors mapped over the upper list by List.rec.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (cvl/definition-ids env) (cvl/theorem-ids env))]
      (is (= #{'nnrat/farkas-cross-vectors-uppers-hold
               'nnrat/farkas-cross-vectors-reduced
               'nnrat/farkas-cross-vectors-reduced-holds}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest cross-list-body-retains-list-fold-and-pair-reduction
  (testing "the per-upper fold remains connected to List.rec and the
            pairwise reduced-holds theorem"
    (doseq [symbol ['data/List.rec
                    'nnrat/farkas-cross-vectors]]
      (is (pos? (body-symbol-count (:value cvl/cross-vectors-list-spec) symbol))
          (str (:name cvl/cross-vectors-list-spec) " body depends on " symbol)))))
