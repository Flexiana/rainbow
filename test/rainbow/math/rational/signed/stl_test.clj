(ns rainbow.math.rational.signed.stl-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.stl-robustness :as ahof-v6]
            [rainbow.math.rational.signed.stl :as iteration]
            [rainbow.algorithms.reference.stl-robustness :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d61-q-learning/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D61 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-v6/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-min-max-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'validation/signed-decide-at-most
             'validation/signed-min
             'validation/signed-max}
           (set (keys definitions))))
    (is (= #{'validation/signed-min-preserved
             'validation/signed-max-preserved}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-v6-robustness-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-v6/theorem-ids checked-environment)]
    (is (= #{'ahof-v6/and-selects-minimum
             'ahof-v6/robustness-values
             'ahof-v6/stl-robustness}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-stl-robustness-detects-violation-and-satisfaction
  ;; Conjunction of satisfied 1/2 and violated -1/4 is violated (min -1/4);
  ;; disjunction is satisfied (max 1/2); negation flips the sign.
  (is (= -1/4 (executable/conjunction 1/2 -1/4)))
  (is (= 1/2 (executable/disjunction 1/2 -1/4)))
  (is (= -1/2 (executable/negation 1/2)))
  (is (false? (executable/satisfied? (executable/conjunction 1/2 -1/4))))
  (is (true? (executable/satisfied? (executable/disjunction 1/2 -1/4)))))
