(ns rainbow.math.rational.nnrat.farkas-vector-partition-pack-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-partition-pack :as vpp]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vpp/extend-environment (:environment checkpoint)))))

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

(deftest reduced-vector-row-packs-into-a-both-sides-data-row
  (testing "the partition bridge's single-row core: a reduced coefficient-
            vector row packs into the data row (AL,(AR,(P,Q))) whose
            projections reduce to AL/AR/P/Q, so farkas-reduced-conditions of
            the one-element packed list is discharged by
            farkas-vector-both-sides-reduce conjoined with truth (defeq-carry).
            This is what lets the bilist bridge feed the already-proved
            partition. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vpp/definition-ids env) (vpp/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-partition-pack} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest partition-pack-retains-row-reduction-dependencies
  (testing "the single-row pack remains connected to its reduced-condition
            and both-sides reduction constructors"
    (doseq [symbol ['nnrat/farkas-vector-both-sides-reduce]]
      (is (pos? (body-symbol-count (:value vpp/partition-pack-spec) symbol))
          (str (:name vpp/partition-pack-spec) " body depends on " symbol)))))
