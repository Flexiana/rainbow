(ns rainbow.math.rational.nnrat.farkas-elim-scaled-coupled-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-scaled-coupled :as scaled]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (scaled/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(defn- contains-symbol? [form symbol]
  "Supplementary source-level guard for premise-use, alongside kernel checks."
  (boolean (some #(= symbol %) (tree-seq coll? seq form))))

(defn- body-symbol-count [form symbol]
  (cond
    (and (vector? form) (= :fn (first form)))
    (body-symbol-count (nth form 2) symbol)
    (coll? form)
    (reduce + (map #(body-symbol-count % symbol) form))
    (= symbol form) 1
    :else 0))

(deftest scaled-coupled-elimination-is-sound-and-complete
  (testing "brick 1 of the general LP FM encoding: eliminating a variable
            coupled to a survivor with a COEFFICIENT (a*v <= w) transfers
            a*max-lb(lowers) <= w onto the survivor, iff both directions,
            kernel-checked and axiom-free"
    (let [env @checked-environment
          ids (merge (scaled/definition-ids env) (scaled/theorem-ids env))]
      (is (= #{'nnrat/farkas-elim-scaled-coupled-reduced
               'nnrat/farkas-elim-scaled-coupled-solvable
               'nnrat/farkas-elim-scaled-coupled-extends
               'nnrat/farkas-elim-scaled-coupled-projects
               'nnrat/farkas-elim-scaled-coupled-solvable-iff}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
      (doseq [[spec premise type-uses?]
              [[scaled/extends-spec 'reduced-feasible true]
               [scaled/projects-spec 'solution true]
               [scaled/solvable-iff-spec 'reduced-feasible false]]]
        (testing (str "premise remains referenced in " (:name spec))
          (when type-uses?
            (is (contains-symbol? (:type spec) premise)))
          (is (contains-symbol? (:value spec) premise))
          (is (pos? (body-symbol-count (:value spec) premise)))))))
