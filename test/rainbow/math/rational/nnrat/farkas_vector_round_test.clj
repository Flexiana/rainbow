(ns rainbow.math.rational.nnrat.farkas-vector-round-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-round :as vr]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vr/extend-environment (:environment checkpoint)))))

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

(deftest one-closed-coefficient-vector-round
  (testing "one Fourier-Motzkin round on the coefficient-vector representation,
            end to end: given the lower/upper next-variable constraints all
            hold at x1 (the k+1 system feasible at this slice), there EXIST
            reduced affine lower/upper lists both satisfied at x2. Composes
            cross-vectors-all-reduced -> adapter-bilist -> partition-fold ->
            partition-list-necessary. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vr/definition-ids env) (vr/theorem-ids env))]
      (is (= #{'nnrat/farkas-vector-round} (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest round-body-retains-each-bridge
  (testing "the end-to-end round remains connected to its reduction, adapter,
            fold, and partition bridges rather than merely having a checked
            proposition of the right type"
    (doseq [symbol ['nnrat/farkas-cross-vectors-all-reduced
                    'nnrat/farkas-vector-adapter-bilist
                    'nnrat/farkas-vector-partition-fold
                    'nnrat/farkas-partition-list-necessary]]
      (is (pos? (body-symbol-count (:value vr/round-spec) symbol))
          (str (:name vr/round-spec) " body depends on " symbol)))))
