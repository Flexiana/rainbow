(ns rainbow.math.rational.nnrat.farkas-elim-affine-list-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as affine-list]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (affine-list/extend-environment (:environment checkpoint)))))

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

(deftest affine-list-elimination-is-sound-and-complete
  (testing "brick 4 of the general LP FM encoding: the one-primal-variable
            elimination step over a LIST of affine upper rows (a*v + s <= b).
            Eliminating v (witness max-lb) is solvable iff every row holds
            at max-lb; the projection maps the per-row argument across the
            list by induction. Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (affine-list/definition-ids env)
                     (affine-list/theorem-ids env))]
      (is (= #{'nnrat/farkas-elim-affine-rows-satisfied
               'nnrat/farkas-elim-affine-list-reduced
               'nnrat/farkas-elim-affine-list-solvable
               'nnrat/farkas-elim-affine-list-extends
               'nnrat/farkas-elim-affine-list-projects
               'nnrat/farkas-elim-affine-list-solvable-iff}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
      (doseq [[spec premise type-uses?]
              [[affine-list/extends-spec 'reduced-feasible true]
               [affine-list/projects-spec 'solution true]
               [affine-list/solvable-iff-spec 'reduced-feasible false]]]
        (testing (str "premise remains referenced in " (:name spec))
          (when type-uses?
            (is (contains-symbol? (:type spec) premise)))
          (is (contains-symbol? (:value spec) premise))
          (is (pos? (body-symbol-count (:value spec) premise)))))))
