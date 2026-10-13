(ns rainbow.math.logic.function-predicate-test
  (:require [clojure.test :refer :all]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib-native :as native]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function-predicate :as predicate]))

(def checked-environment (delay (predicate/build-environment)))

(deftest native-function-predicates-are-reducible-axiom-free-data
  (let [report (predicate/report)]
    (is (= :passed (:status report)))
    (is (= '[function/involutive function/injective
             function/surjective function/bijective]
           (:predicates report)))
    (is (every? empty? (vals (:axioms report))))
    (doseq [name (:predicates report)]
      (let [id (environment/resolve-id @checked-environment name)
            declaration (environment/declaration @checked-environment id)]
        (is (= :definition (:rainbow/kind declaration)))
        (is (= :reducible (:rainbow/transparency declaration)))
        (is (= :checked
               (:status (kernel/check @checked-environment
                                      (:rainbow/value declaration)
                                      (:rainbow/type declaration)
                                      (set (:rainbow/universes declaration))))))))))

(deftest foreign-function-predicate-resolves-to-checked-native-identity
  (let [statement
        {:rainbow.catalog/kind :statement
         :foreign/name "Example.injective"
         :foreign/universes ["u" "v"]
         :foreign/type-fingerprint "test:injective"
         :foreign/type
         [:pi [:sort [:param "u"]]
          [:pi [:sort [:param "v"]]
           [:pi [:pi [:bound 1] [:bound 1] :explicit]
            [:app
             [:app
              [:app [:const "Function.Injective"
                     [[:param "u"] [:param "v"]]]
               [:bound 2]]
              [:bound 1]]
             [:bound 0]]
            :explicit]
           :implicit]
          :implicit]
         :foreign/value :redacted}
        result (native/nativeize-statement-type @checked-environment statement)]
    (is (= :nativeized (:status result)))
    (is (= ["Function.Injective"] (:foreign/constants result)))
    (is (= :checked (get-in result [:kernel :status])))))
