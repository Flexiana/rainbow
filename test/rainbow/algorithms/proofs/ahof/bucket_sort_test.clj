(ns rainbow.algorithms.proofs.ahof.bucket-sort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bucket-sort :as bs]
            [rainbow.algorithms.reference.bucket-sort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bucket-sort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bs/definition-ids checked-environment)
        theorems (bs/theorem-ids checked-environment)]
    (is (= #{'bucket-sort/bucket-precedes?} (set (keys definitions))))
    (is (= #{'bucket-sort/lower-bucket-first
             'bucket-sort/preceding-bucket-index-at-most
             'bucket-sort/higher-bucket-later}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bucket-sort
  (is (true? (executable/bucket-precedes? 1 4)))
  (is (false? (executable/bucket-precedes? 4 1)))
  (is (= [0.12 0.17 0.21 0.23 0.26 0.39 0.68 0.72 0.78 0.94]
         (executable/bucket-sort [0.78 0.17 0.39 0.26 0.72 0.94 0.21 0.12 0.23 0.68] 10))))
