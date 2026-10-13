(ns rainbow.math.rational.nnrat.farkas-elim-chain-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-chain :as elim]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (elim/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- contains-symbol? [form symbol]
  "Supplementary source-level guard for chain witness and premise use."
  (boolean (some #(= symbol %) (tree-seq coll? seq form))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest arbitrary-finite-elimination-chain-is-native-axiom-free
  (let [env @checked-environment
        definitions (elim/definition-ids env)
        theorems (elim/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'nnrat/farkas-elim-chain-lower
             'nnrat/farkas-elim-chain-feasible
             'nnrat/farkas-elim-chain-open-reduced
             'nnrat/farkas-elim-chain-open-solvable
             'nnrat/farkas-elim-chain-reduced
             'nnrat/farkas-elim-chain-solvable}
           (set (keys definitions))))
    (is (= #{'nnrat/farkas-elim-chain-open-extends
             'nnrat/farkas-elim-chain-open-projects
             'nnrat/farkas-elim-chain-open-solvable-iff
             'nnrat/farkas-elim-chain-extends
             'nnrat/farkas-elim-chain-projects
             'nnrat/farkas-elim-chain-solvable-iff}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))
    (doseq [[spec symbols]
            [[elim/open-extends-spec ['reduced-feasible]]
             [elim/open-projects-spec ['solution]]
             [elim/open-solvable-iff-spec ['evidence]]
             [elim/extends-spec ['reduced-feasible]]
             [elim/projects-spec ['solution 'terminal-evidence]]
             [elim/solvable-iff-spec ['evidence]]]]
      (doseq [symbol symbols]
        (is (contains-symbol? (:value spec) symbol)
            (str (:name spec) " references " symbol))
        (is (pos? (body-symbol-count (:value spec) symbol)))))))
