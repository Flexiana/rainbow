(ns rainbow.math.rational.nnrat.farkas-vector-step-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-step :as vs]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vs/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- body-symbol-count [form symbol]
  ;; Binder occurrences do not establish a proof dependency.
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest the-round-is-wired-into-the-over-variable-recursion
  (testing "the recursion step: farkas-vector-step composes one elimination
            round with the unit-column re-presentation (unpacking the round's
            existential) into a closed step in the held next-variable
            representation; farkas-vector-feasible-step wraps it to
            Feasible(succ k) -> Feasible k; farkas-vector-eliminate instantiates
            farkas-eliminate-all to conclude Feasible n -> Feasible 0. The
            coefficient-vector round is wired into the recursion skeleton.
            Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vs/definition-ids env) (vs/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-feasible
               'nnrat/farkas-vector-step
               'nnrat/farkas-vector-feasible-step
               'nnrat/farkas-vector-eliminate}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest vector-chain-bodies-retain-their-structural-dependencies
  (testing "checked declarations are wired to the intended proof chain;
            kernel acceptance alone would not catch an unrelated closed proof"
    (let [checks [[vs/feasible-step-spec
                   ['nnrat/farkas-vector-step]]
                  [vs/eliminate-spec
                   ['nnrat/farkas-eliminate-all
                    'nnrat/farkas-vector-feasible-step]]]]
      (doseq [[spec symbols] checks
              symbol symbols]
        (is (pos? (body-symbol-count (:value spec) symbol))
            (str (:name spec) " body depends on " symbol))))))
