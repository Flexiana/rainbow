(ns rainbow.accounting-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.accounting :as accounting]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def base (delay (proposition/build-environment)))

(defn- add! [environment aliases surface-type surface-value provenance]
  (let [type (:term (elaborate/core-expression environment surface-type))
        value (:term (elaborate/core-expression environment surface-value))
        result (kernel/add-declaration
                environment
                {:rainbow/kind :theorem
                 :rainbow/aliases aliases
                 :rainbow/universes []
                 :rainbow/type type
                 :rainbow/value value
                 :rainbow/transparency :opaque
                 :rainbow/dependencies (into (term/constants type)
                                             (term/constants value))
                 :rainbow/provenance provenance
                 :rainbow/schema-version 1})]
    (assert (= :accepted (:status result)) (pr-str result))
    [(:environment result) (get-in result [:declaration :rainbow/id])]))

(def truth (proposition/truth))
(def trivial (proposition/const* 'proposition/trivial []))

;; two DIFFERENT proof terms of the same statement `truth -> truth`
(def identity-proof
  (proposition/lam [['evidence truth]] 'evidence))
(def constant-proof
  (proposition/lam [['ignored truth]] trivial))

(deftest aliases-never-inflate-the-proof-object-count
  (let [[environment id]
        (add! @base #{'test/one 'test/one-again} truth trivial
              {:origin :native :producer :test})
        report (accounting/account environment [id])]
    (is (= 1 (:accounting/declarations report)))
    (is (= 1 (:accounting/proof-objects report)))
    (is (= {} (:accounting/coincident report)))
    (testing "the second alias is reported, not silently dropped"
      (is (= {id ["test/one" "test/one-again"]} (:accounting/aliased report))))))

(deftest coincident-statements-never-inflate-the-statement-count
  (let [statement (proposition/arrow truth truth)
        [environment first-id]
        (add! @base #{'test/identity} statement identity-proof
              {:origin :native :producer :test})
        [environment second-id]
        (add! environment #{'test/constant} statement constant-proof
              {:origin :native :producer :test})
        report (accounting/account environment [first-id second-id])]
    (testing "two genuinely different proofs are two proof objects"
      (is (= 2 (:accounting/proof-objects report)))
      (is (not= first-id second-id)))
    (testing "but they inhabit one statement, and the report says so"
      (is (= 1 (:accounting/statements report)))
      (is (= 1 (count (:accounting/coincident report))))
      (is (= #{first-id second-id}
             (set (first (vals (:accounting/coincident report)))))))
    (is (true? (accounting/inflated? report)))))

(deftest foreign-declarations-and-native-abstractions-are-counted-apart
  (let [[environment foreign-id]
        (add! @base #{'test/foreign-mapped} truth trivial
              {:origin :native :producer :test
               :foreign/system :lean :foreign/name "Some.Mathlib.Lemma"})
        [environment native-id]
        (add! environment #{'test/native-abstraction}
              (proposition/arrow truth truth) identity-proof
              {:origin :native :producer :test})
        report (accounting/account environment [foreign-id native-id])]
    (is (= 1 (:accounting/foreign-declarations report)))
    (is (= 1 (:accounting/native-abstractions report)))
    (is (= 2 (:accounting/proof-objects report)))
    (is (= 2 (:accounting/statements report)))
    (is (false? (accounting/inflated? report)))))

(deftest accounting-can-report-the-cohort-logical-profile
  (let [[environment id]
        (add! @base #{'test/profiled} truth trivial
              {:origin :native :producer :test})
        report (accounting/account environment [id] :constructive)]
    (is (= {:constructive 1}
           (get-in report [:accounting/logical :logical/by-profile])))
    (is (empty? (get-in report [:accounting/logical :logical/outside])))))

(deftest accounting-refuses-declarations-outside-the-environment
  (is (= :accounting/unknown-declaration
         (:error/category
          (try (accounting/account @base ["sha256:not-in-this-environment"])
               (catch clojure.lang.ExceptionInfo exception
                 (ex-data exception)))))))
