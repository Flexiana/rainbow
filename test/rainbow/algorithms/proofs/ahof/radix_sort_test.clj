(ns rainbow.algorithms.proofs.ahof.radix-sort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.radix-sort :as radix]
            [rainbow.algorithms.reference.radix-sort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          radix/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest radix-sort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (radix/definition-ids checked-environment)
        theorems (radix/theorem-ids checked-environment)]
    (is (= #{'radix-sort/digit-precedes?} (set (keys definitions))))
    (is (= #{'radix-sort/smaller-digit-precedes 'radix-sort/preceding-digit-at-most
             'radix-sort/larger-digit-follows}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-radix-sort
  (is (true? (executable/digit-precedes? 2 7)))
  (is (false? (executable/digit-precedes? 7 2)))
  (is (= [2 24 45 66 75 90 170 802]
         (executable/radix-sort [170 45 75 90 802 24 2 66] 3))))
