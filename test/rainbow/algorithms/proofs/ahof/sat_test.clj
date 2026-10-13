(ns rainbow.algorithms.proofs.ahof.sat-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.sat :as sat]
            [rainbow.algorithms.reference.sat :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sat/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest sat-clause-satisfaction-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sat/definition-ids checked-environment)
        theorems (sat/theorem-ids checked-environment)]
    (is (= #{'sat/clause-satisfied?} (set (keys definitions))))
    (is (= #{'sat/clause-cons 'sat/clause-satisfiable
             'sat/clause-unsatisfiable 'sat/clause-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-sat-checks-satisfaction
  (is (true? (executable/clause-satisfied? [false true false])))
  (is (false? (executable/clause-satisfied? [false false])))
  ;; CNF (a OR b) AND (NOT a OR b): satisfied by a=false, b=true.
  (let [clauses-of (fn [{:keys [a b]}] [[a b] [(not a) b]])
        assignment (executable/satisfying-assignment [:a :b] clauses-of)]
    (is (some? assignment))
    (is (true? (executable/formula-satisfied? (clauses-of assignment))))))
