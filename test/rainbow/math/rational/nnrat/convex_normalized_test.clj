(ns rainbow.math.rational.nnrat.convex-normalized-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.convex-normalized :as normalized]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (normalized/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest normalized-two-point-convex-bracket-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (normalized/definition-ids env)
                   (normalized/theorem-ids env))]
    (is (= #{'nnrat/two-point-normalized-at-least-min
             'nnrat/two-point-normalized-at-most-max}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " kernel check"))
      (is (= #{} (kernel/axioms env id)) (str name " axioms")))))
