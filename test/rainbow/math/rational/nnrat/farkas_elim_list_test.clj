(ns rainbow.math.rational.nnrat.farkas-elim-list-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim]))

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

(deftest list-sized-bound-elimination-is-native-axiom-free
  (let [env @checked-environment
        definitions (elim/definition-ids env)
        theorems (elim/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'nnrat/ge-all
             'nnrat/le-all
             'nnrat/max-lb
             'nnrat/min-ub
             'nnrat/farkas-elim-list-reduced
             'nnrat/farkas-elim-list-solvable}
           (set (keys definitions))))
    (is (= #{'nnrat/zero-at-most
             'nnrat/max-lb-is-upper
             'nnrat/max-lb-least
             'nnrat/le-all-antitone
             'nnrat/min-ub-is-lower
             'nnrat/min-ub-greatest
             'nnrat/farkas-elim-list-extends
             'nnrat/farkas-elim-list-projects
             'nnrat/farkas-elim-list-solvable-iff}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
