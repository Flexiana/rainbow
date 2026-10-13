(ns rainbow.math.rational.nnrat.farkas-reduce-align-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-reduce-align :as align]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (align/extend-environment (:environment checkpoint)))))

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

(deftest structured-elimination-round-closes
  (testing "piece (i) data-representation alignment: the map to 4-tuple
            both-sides rows, the fold-alignment lemma, and the composed
            structured elimination round (cross holds -> reduced affine
            system, link fully discharged). Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (align/definition-ids env) (align/theorem-ids env))]
      (is (= #{'nnrat/farkas-structured-to-both-sides
               'nnrat/farkas-reduce-align
               'nnrat/farkas-eliminate-structured}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(deftest structured-round-retains-bridge-and-alignment-cores
  (testing "the composed structured round remains connected to its bridge,
            list-reduction, and alignment components"
    (doseq [symbol ['nnrat/farkas-bridge-list-necessary
                    'nnrat/farkas-reduce-list-necessary
                    'nnrat/farkas-reduce-align]]
      (is (pos? (body-symbol-count (:value align/eliminate-structured-spec) symbol))
          (str (:name align/eliminate-structured-spec) " body depends on " symbol)))))
