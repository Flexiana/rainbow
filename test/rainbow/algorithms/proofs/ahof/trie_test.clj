(ns rainbow.algorithms.proofs.ahof.trie-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.trie :as trie]
            [rainbow.algorithms.reference.trie :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          trie/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest trie-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (trie/definition-ids checked-environment)
        theorems (trie/theorem-ids checked-environment)]
    (is (= #{'trie/is-word?} (set (keys definitions))))
    (is (= #{'trie/complete-terminal-is-word 'trie/prefix-not-word
             'trie/incomplete-path-not-word}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-trie
  (is (true? (executable/is-word? true true)))
  (is (false? (executable/is-word? true false)))
  (let [t (-> executable/empty-trie
              (executable/insert "cat")
              (executable/insert "car")
              (executable/insert "card"))]
    (is (true? (executable/contains-word? t "cat")))
    (is (true? (executable/contains-word? t "car")))
    ;; "ca" is a prefix but not a stored word
    (is (false? (executable/contains-word? t "ca")))
    (is (true? (executable/has-prefix? t "ca")))
    (is (false? (executable/contains-word? t "dog")))))
