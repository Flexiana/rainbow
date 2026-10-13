(ns rainbow.math.rational.nnrat.farkas-elim-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim :as elim]))

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

(deftest fixed-two-lower-two-upper-elimination-is-native-axiom-free
  (let [env @checked-environment
        definitions (elim/definition-ids env)
        theorems (elim/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'nnrat/farkas-elim-two-lower-two-upper-system
             'nnrat/farkas-elim-two-lower-two-upper-reduced
             'nnrat/farkas-elim-two-lower-two-upper-solvable}
           (set (keys definitions))))
    (is (= #{'nnrat/farkas-elim-two-lower-two-upper-extends
             'nnrat/farkas-elim-two-lower-two-upper-projects
             'nnrat/farkas-elim-two-lower-two-upper-solvable-iff}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
