(ns rainbow.coverage.guard-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.coverage.total-test :as total]))

(defn- record [text]
  (with-redefs [slurp (constantly text)]
    (#'total/ns-and-requires "fixture.clj")))

(deftest imports-come-only-from-the-namespace-form
  (is (= #{"rainbow.real"}
         (second (record "(ns fixture (:require [rainbow.real :as r]))
                          (def links '[rainbow.fake])")))))

(deftest all-imports-are-read-without-a-character-limit
  (is (= #{"rainbow.first" "rainbow.last"}
         (second (record (str "(ns fixture (:require [rainbow.first] "
                              (apply str (repeat 7000 " ")) "[rainbow.last]))"))))))

(deftest prefix-and-symbol-libspecs-are-supported
  (is (= #{"rainbow.one" "rainbow.two" "rainbow.three" "rainbow.four"}
         (second (record "(ns fixture (:require (rainbow one [two :as t]) rainbow.three)
                                       (:use [rainbow.four]))")))))

(deftest refer-options-are-not-prefix-libspecs
  (is (= #{"rainbow.real"}
         (second (record "(ns fixture (:require [rainbow.real :refer [f g]]))")))))

(deftest reading-an-inventory-does-not-evaluate-reader-forms
  (is (thrown-with-msg? RuntimeException #"EvalReader not allowed"
               (record "#=(throw (Exception. \"must not evaluate\"))"))))

(def ^:private proof ["rainbow.proof" #{} "(defn extend-environment [env] env)"])
(def ^:private test-route ["rainbow.proof-test" #{"rainbow.proof"} ""])

(deftest coverage-rejects-empty-discovery-and-pending-exemptions
  (is (empty? (#'total/coverage-problems [proof] [test-route] #{})))
  (is (:no-source (#'total/coverage-problems [] [test-route] #{})))
  (is (:no-tests (#'total/coverage-problems [proof] [] #{})))
  (is (:no-proof-modules (#'total/coverage-problems [["empty" #{} ""]] [test-route] #{})))
  (let [problems (#'total/coverage-problems [proof] [["empty-test" #{} ""]] #{"rainbow.proof"})]
    (is (= ["rainbow.proof"] (:pending problems)))
    (is (= ["rainbow.proof"] (:missing problems)))))
