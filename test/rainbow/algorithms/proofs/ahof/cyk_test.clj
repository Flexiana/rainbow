(ns rainbow.algorithms.proofs.ahof.cyk-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.cyk :as cyk]
            [rainbow.algorithms.reference.cyk :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          cyk/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest cyk-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (cyk/definition-ids checked-environment)
        theorems (cyk/theorem-ids checked-environment)]
    (is (= #{'cyk/rule-applies?} (set (keys definitions))))
    (is (= #{'cyk/rule-applies-both-derivable 'cyk/rule-fails-left-missing
             'cyk/rule-fails-right-missing}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-cyk
  (is (true? (executable/rule-applies? true true)))
  (is (false? (executable/rule-applies? false true)))
  ;; balanced parens grammar (CNF): S -> L R' | S S ; R' -> S R ; L -> ( ; R -> )
  (let [unit {\( #{:L} \) #{:R}}
        binary #{[:S :L :R] [:S :L :X] [:X :S :R] [:S :S :S]}]
    (is (true? (executable/recognize? (vec "()") :S unit binary)))
    (is (true? (executable/recognize? (vec "(())") :S unit binary)))
    (is (false? (executable/recognize? (vec "(()") :S unit binary)))))
