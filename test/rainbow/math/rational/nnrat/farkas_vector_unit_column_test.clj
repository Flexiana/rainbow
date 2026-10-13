(ns rainbow.math.rational.nnrat.farkas-vector-unit-column-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-unit-column :as vuc]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vuc/extend-environment (:environment checkpoint)))))

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

(deftest affine-output-re-presents-as-held-next-variable-constraints
  (testing "the unit-column re-presentation: a round's satisfied affine
            lower/upper rows (a,(s,x)) at x2 re-present as HELD next-variable
            coefficient constraints (a,(x,(s,nil))) at x2, carrying the
            constant s as a unit-column coefficient (value nnrat/one). Each
            coupling transports across s ~ s*1 + 0. This makes the round's
            output feed its own input, closing the round loop.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vuc/definition-ids env) (vuc/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-unit-repr
               'nnrat/farkas-vector-unit-column-lower
               'nnrat/farkas-vector-unit-column-upper}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest unit-column-bodies-retain-induction-and-transport-bridges
  (testing "both transports remain connected to list induction, their
            satisfaction premises, and equivalence/order transport"
    (doseq [[spec symbols]
            [[vuc/unit-column-lower-spec
              ['data/List.rec
               'nnrat/farkas-elim-affine-lower-rows-satisfied
               'nnrat/at-most-respects-equivalence]]
             [vuc/unit-column-upper-spec
              ['data/List.rec
               'nnrat/farkas-elim-affine-rows-satisfied
               'nnrat/at-most-respects-equivalence]]]]
      (doseq [symbol symbols]
        (is (pos? (body-symbol-count (:value spec) symbol))
            (str (:name spec) " body depends on " symbol))))))
