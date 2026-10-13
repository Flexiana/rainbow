(ns rainbow.math.rational.nnrat.farkas-vector-adapter-bilist-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-bilist :as vab]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (vab/extend-environment (:environment checkpoint)))))

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

(deftest whole-round-reduced-conditions-become-the-flat-descriptor-fold
  (testing "the partition bridge adapter (bilist): the whole round's
            farkas-cross-vectors-all-reduced-conds (a fold over lowers of the
            per-lower cross-vectors-reduced fold) implies all-input-rows of the
            concatenated per-lower descriptor lists. Proof folds the per-upper
            adapter over the lower list, joining with the append lemma
            (all-input-rows distributes over list/append). The concatenated
            list + this proof are the bridge fold's exact input, so
            adapter+fold+partition compose into one closed coefficient-vector
            round. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (vab/definition-ids env) (vab/theorem-ids env))]
      (is (= #{'nnrat/farkas-adapter-descs-bilist
               'nnrat/farkas-vector-input-rows-append
               'nnrat/farkas-vector-adapter-bilist}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest bilist-adapter-retains-append-and-cross-fold-dependencies
  (testing "the adapter proof remains connected to the append transport and
            the per-lower/per-upper cross-vector folds"
    (doseq [[spec symbols]
            [[vab/input-rows-append-spec
              ['data/List.rec]]
             [vab/adapter-bilist-spec
              ['nnrat/farkas-cross-vectors-all-reduced-conds
               'nnrat/farkas-vector-adapter-list
               'nnrat/farkas-vector-input-rows-append]]]]
      (doseq [symbol symbols]
        (is (pos? (body-symbol-count (:value spec) symbol))
            (str (:name spec) " body depends on " symbol))))))
