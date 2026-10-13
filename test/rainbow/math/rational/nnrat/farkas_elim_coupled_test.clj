(ns rainbow.math.rational.nnrat.farkas-elim-coupled-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as elim]))

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
  "Supplementary source-level guard for dependent elimination premises."
  (boolean (some #(= symbol %) (tree-seq coll? seq form))))

(deftest coupled-elimination-transfers-a-bound-axiom-free
  (let [env @checked-environment
        definitions (elim/definition-ids env)
        theorems (elim/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'nnrat/farkas-elim-coupled-reduced
             'nnrat/farkas-elim-coupled-solvable}
           (set (keys definitions))))
    (is (= #{'nnrat/farkas-elim-coupled-extends
             'nnrat/farkas-elim-coupled-projects
             'nnrat/farkas-elim-coupled-solvable-iff}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))
    (doseq [[spec premise type-uses?]
            [[elim/extends-spec 'reduced-feasible true]
             [elim/projects-spec 'solution true]
             [elim/solvable-iff-spec 'reduced-feasible false]]]
      (when type-uses?
        (is (contains-symbol? (:type spec) premise)))
      (is (contains-symbol? (:value spec) premise)))))
