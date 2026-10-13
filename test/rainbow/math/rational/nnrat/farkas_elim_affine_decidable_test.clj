(ns rainbow.math.rational.nnrat.farkas-elim-affine-decidable-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-affine-decidable :as decidable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (decidable/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- contains-symbol? [form symbol]
  "Supplementary source-level guard for both constructive decision branches."
  (boolean (some #(= symbol %) (tree-seq coll? seq form))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest affine-list-feasibility-is-decidable
  (testing "brick 4b of the general LP FM encoding: feasibility of the
            affine-row elimination is decidable (the Farkas alternative) --
            each row's coupling is a decidable nnrat comparison, a finite
            conjunction of decidables is decidable, transported through the
            brick-4 solvable-iff. The negative branch is the infeasibility
            certificate. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (decidable/definition-ids env)
                     (decidable/theorem-ids env))]
      (is (= #{'nnrat/farkas-elim-affine-rows-decidable
               'nnrat/farkas-elim-affine-list-solvable-or-not}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
      (testing "decision branches and recursive inputs remain referenced"
        (doseq [[spec symbols]
                [[decidable/rows-decidable-spec ['rows 'value]]
                 [decidable/solvable-or-not-spec
                  ['lowers 'rows 'red-proof 'not-red 'sol-proof]]]]
          (doseq [symbol symbols]
            (is (contains-symbol? (:value spec) symbol)
                (str (:name spec) " references " symbol))
            (is (pos? (body-symbol-count (:value spec) symbol))))))))
