(ns rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce :as vbsr]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vbsr/extend-environment (:environment checkpoint)))))

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

(deftest reduced-vector-row-reduces-to-a-lower-or-upper-disjunction
  (testing "the coefficient-vector partition's per-row reduction: a reduced
            both-sides vector row with x2-headed tails reduces (grouping +
            farkas-both-sides-reduce, no new arithmetic) to the disjunction a
            LOWER row in x2 (AL<=AR) OR an UPPER row in x2 (AR<=AL) -- exactly
            farkas-partition-row's input shape. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vbsr/definition-ids env) (vbsr/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-both-sides-reduce} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest reduction-body-retains-farkas-core
  (testing "the vector reduction remains an application of the generic
            both-sides reduction, rather than an unrelated closed proof"
    (is (pos? (body-symbol-count
               (:value vbsr/vector-both-sides-reduce-spec)
               'nnrat/farkas-both-sides-reduce)))))
