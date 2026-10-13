(ns rainbow.algorithms.proofs.ahof.word-break-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.word-break :as wb]
            [rainbow.algorithms.reference.word-break :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          wb/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest word-break-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (wb/definition-ids checked-environment)
        theorems (wb/theorem-ids checked-environment)]
    (is (= #{'word-break/split-works?} (set (keys definitions))))
    (is (= #{'word-break/split-works-both-hold
             'word-break/split-fails-prefix-unbreakable
             'word-break/split-fails-suffix-not-word}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-word-break
  (is (true? (executable/split-works? true true)))
  (is (false? (executable/split-works? false true)))
  ;; classic: "leetcode" with {leet, code} -> true; "catsandog" with
  ;; {cats, dog, sand, and, cat} -> false
  (is (true? (executable/word-break? "leetcode" #{"leet" "code"})))
  (is (false? (executable/word-break? "catsandog"
                                      #{"cats" "dog" "sand" "and" "cat"}))))
