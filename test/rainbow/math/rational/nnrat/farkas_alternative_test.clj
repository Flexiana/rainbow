(ns rainbow.math.rational.nnrat.farkas-alternative-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-alternative :as alternative]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (alternative/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- contains-symbol? [form symbol]
  "Supplementary source-level guard for both Farkas branches."
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

(deftest constructive-farkas-alternative-is-native-axiom-free
  (let [env @checked-environment
        definitions (alternative/definition-ids env)
        theorems (alternative/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= {} definitions))
    (is (= #{'nat/at-most-decision-complete
             'nnrat/at-most-decidable
             'nnrat/farkas-upper-rest-decidable
             'nnrat/le-all-decidable
             'nnrat/farkas-elim-list-reduced-decidable
             'nnrat/farkas-elim-chain-feasible-decidable
             'nnrat/farkas-elim-chain-reduced-decidable
             'nnrat/farkas-elim-chain-infeasibility-certificate
             'nnrat/farkas-elim-chain-solvable-or-not
             'nnrat/farkas-elim-chain-zero-instance-solvable
             'nnrat/farkas-elim-chain-unit-zero-instance-not-reduced
             'nnrat/farkas-elim-chain-unit-zero-instance-not-solvable}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " is kernel-checked"))
      (is (= #{} (kernel/axioms env id)) (str name " is axiom-free")))))

(deftest both-alternative-branches-have-closed-instances
  (let [env @checked-environment
        theorems (alternative/theorem-ids env)]
    ;; These are closed propositions, not assumptions supplied to the general
    ;; alternative: zero solves the first system, while 1 <= x <= 0 refutes the
    ;; second through the collapsed-condition certificate.
    (doseq [name ['nnrat/farkas-elim-chain-zero-instance-solvable
                  'nnrat/farkas-elim-chain-unit-zero-instance-not-reduced
                  'nnrat/farkas-elim-chain-unit-zero-instance-not-solvable]]
      (let [id (get theorems name)]
        (is (some? id) (str name " is declared"))
        (is (checked? env id) (str name " is kernel-checked"))
        (is (= #{} (kernel/axioms env id)) (str name " is axiom-free"))))
    (testing "general alternative consumes both decision branches"
      (is (<= 2 (symbol-count (:value alternative/chain-solvable-or-not-spec)
                              'reduced-proof)))
      (is (<= 2 (symbol-count (:value alternative/chain-solvable-or-not-spec)
                              'not-reduced-proof)))
      (is (<= 2 (symbol-count
                  (:value alternative/chain-infeasibility-certificate-spec)
                  'not-reduced)))
      (is (pos? (body-symbol-count
                 (:value alternative/chain-solvable-or-not-spec)
                 'reduced-proof)))
      (is (pos? (body-symbol-count
                 (:value alternative/chain-solvable-or-not-spec)
                 'not-reduced-proof)))
      (is (pos? (body-symbol-count
                 (:value alternative/chain-infeasibility-certificate-spec)
                 'not-reduced))))))
