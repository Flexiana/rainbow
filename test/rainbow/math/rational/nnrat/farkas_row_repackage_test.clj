(ns rainbow.math.rational.nnrat.farkas-row-repackage-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-row-repackage :as repackage]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (repackage/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- contains-symbol? [form symbol]
  "Supplementary source-level guard for both equivalence directions."
  (boolean (some #(= symbol %) (tree-seq coll? seq form))))

(defn- symbol-count [form symbol]
  (count (filter #(= symbol %) (tree-seq coll? seq form))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest row-repackaging-holds-up-to-equivalence
  (testing "brick 5a of the general LP FM encoding, the crux: the two
            coupling forms a*m + (c*w + d) <= b and c*w + (a*m + d) <= b are
            equivalent for all operands, transporting <= across the nnrat
            reassociation ~ via at-most-respects-equivalence. Kernel-checked,
            axiom-free"
    (let [env @checked-environment
          ids (merge (repackage/definition-ids env)
                     (repackage/theorem-ids env))]
      (is (= #{'nnrat/farkas-row-repackage-iff}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
      (testing "both transported inequality premises remain referenced"
        (is (contains-symbol? (:value repackage/repackage-iff-spec) 'ordered))
        (is (<= 2 (symbol-count (:value repackage/repackage-iff-spec)
                                'ordered))
            "each equivalence direction must consume its premise")
        (is (<= 2 (body-symbol-count (:value repackage/repackage-iff-spec)
                                      'ordered))
            "both premise uses must occur outside lambda binders"))))
