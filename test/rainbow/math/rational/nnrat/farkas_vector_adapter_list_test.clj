(ns rainbow.math.rational.nnrat.farkas-vector-adapter-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-list :as val]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (val/extend-environment (:environment checkpoint)))))

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

(deftest per-lower-reduced-conditions-become-the-flat-descriptor-fold
  (testing "the partition bridge adapter (per-upper list): for one lower row
            against a list of next-variable upper constraints, the nested
            per-upper reduced conditions (farkas-cross-vectors-reduced over the
            mapped uppers) transport, conjunct by conjunct via defeq
            (reduced-at(map-c upper) IS input-row(descriptor)), into the flat
            all-input-rows fold over the per-upper descriptor list. This is
            what feeds the bridge fold. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (val/definition-ids env) (val/theorem-ids env))]
      (is (= #{'nnrat/farkas-adapter-map-uppers
               'nnrat/farkas-adapter-descs-of-lower
               'nnrat/farkas-vector-adapter-list}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest adapter-list-retains-recursive-and-reduction-bridges
  (testing "the per-list adapter retains list recursion and the nested
            reduced-condition bridge"
    (doseq [[spec symbols]
            [[val/map-c-list-spec ['data/List.rec]]
             [val/descs-of-lower-spec ['data/List.rec]]
             [val/adapter-list-spec
              ['data/List.rec 'nnrat/farkas-cross-vectors-reduced]]]]
      (doseq [symbol symbols]
        (is (pos? (body-symbol-count (:value spec) symbol))
            (str (:name spec) " body depends on " symbol))))))
