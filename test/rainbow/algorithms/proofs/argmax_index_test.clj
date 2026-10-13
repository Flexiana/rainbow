(ns rainbow.algorithms.proofs.argmax-index-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.algorithms.reference.argmax-index :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          argmax-index/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest argmax-index-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (argmax-index/definition-ids checked-environment)
        theorems (argmax-index/theorem-ids checked-environment)]
    (is (= #{'argmax-index/argmax-from 'argmax-index/argmax-index}
           (set (keys definitions))))
    (is (= #{'argmax-index/argmax-middle 'argmax-index/argmax-first
             'argmax-index/argmax-last}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-argmax-index-reduces
  (is (= 1 (executable/argmax-index [5 7 4])))
  (is (= 0 (executable/argmax-index [8 3 2])))
  (is (= 2 (executable/argmax-index [2 4 9]))))
