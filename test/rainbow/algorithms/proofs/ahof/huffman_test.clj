(ns rainbow.algorithms.proofs.ahof.huffman-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.huffman :as huffman]
            [rainbow.algorithms.reference.huffman :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          huffman/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest huffman-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (huffman/definition-ids checked-environment)
        theorems (huffman/theorem-ids checked-environment)]
    (is (= #{'huffman/merge-frequency 'huffman/merge-first?}
           (set (keys definitions))))
    (is (= #{'huffman/merge-example 'huffman/merges-lower-first
             'huffman/greedy-picks-minimum}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-huffman
  (is (= 5 (executable/merge-frequency 2 3)))
  (is (true? (executable/merge-first? 2 5)))
  ;; frequencies [1 1 2 4]: merges 1+1=2, 2+2=4, 4+4=8; total weighted length 14
  (is (= 14 (executable/code-lengths [1 1 2 4]))))
