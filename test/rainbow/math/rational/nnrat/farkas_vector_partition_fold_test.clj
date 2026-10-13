(ns rainbow.math.rational.nnrat.farkas-vector-partition-fold-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-partition-fold :as vpf]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vpf/extend-environment (:environment checkpoint)))))

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

(deftest reduced-vector-rows-fold-into-the-affine-partition-input
  (testing "the partition bridge fold: a list of reduced (lower,upper)
            descriptors whose reduced both-sides vector rows all hold at x2
            folds (List.rec, farkas-vector-both-sides-reduce per row) into the
            packed both-sides DATA list plus its farkas-reduced-conditions
            proof -- exactly the two inputs farkas-partition-list-necessary
            consumes. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vpf/definition-ids env) (vpf/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-partition-input-rows
               'nnrat/farkas-vector-partition-packed
               'nnrat/farkas-vector-partition-fold}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest partition-fold-retains-recursion-and-row-reduction
  (testing "the fold body remains connected to list induction, row reduction,
            and the reduced-condition constructor"
    (doseq [symbol ['data/List.rec
                    'nnrat/farkas-vector-both-sides-reduce
                    'nnrat/farkas-reduced-conditions]]
      (is (pos? (body-symbol-count (:value vpf/partition-fold-spec) symbol))
          (str (:name vpf/partition-fold-spec) " body depends on " symbol)))))
