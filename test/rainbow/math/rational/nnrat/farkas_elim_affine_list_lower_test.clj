(ns rainbow.math.rational.nnrat.farkas-elim-affine-list-lower-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list-lower :as lower]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lower/extend-environment (:environment checkpoint)))))

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

(deftest affine-lower-list-elimination-is-sound-and-complete
  (testing "brick 5b of the general LP FM encoding: the one-variable step
            over a LIST of affine LOWER rows (w <= a*v + s), the mirror of
            brick 4. Eliminating v (witness min-ub of the uppers) is
            solvable iff every lower row holds at min-ub. Kernel-checked,
            axiom-free"
    (let [env @checked-environment
          ids (merge (lower/definition-ids env) (lower/theorem-ids env))]
      (is (= #{'nnrat/farkas-elim-affine-lower-rows-satisfied
               'nnrat/farkas-elim-affine-list-lower-reduced
               'nnrat/farkas-elim-affine-list-lower-solvable
               'nnrat/farkas-elim-affine-list-lower-extends
               'nnrat/farkas-elim-affine-list-lower-projects
               'nnrat/farkas-elim-affine-list-lower-solvable-iff}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
      (doseq [[spec premise type-uses?]
              [[lower/extends-spec 'reduced-feasible true]
               [lower/projects-spec 'solution true]
               [lower/solvable-iff-spec 'reduced-feasible false]]]
        (testing (str "premise remains referenced in " (:name spec))
          (when type-uses?
            (is (contains-symbol? (:type spec) premise)))
          (is (contains-symbol? (:value spec) premise))
          (is (pos? (body-symbol-count (:value spec) premise)))))))
