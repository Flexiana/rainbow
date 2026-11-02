(ns rainbow.show-errors-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.main :as main]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]))

(deftest unknown-modules-return-actionable-failure
  (with-redefs [checkpoint/load-checkpoint (constantly {:status :replayed :environment (environment/empty-environment)})]
    (let [result (atom nil)
          text (with-out-str (reset! result (#'main/show-main ["some/theorem" "rainbow.no.such.module"])))]
      (is (false? @result))
      (is (re-find #"FAIL show" text))
      (is (re-find #"rainbow.no.such.module|rainbow/no/such/module" text))
      (is (re-find #"[Cc]heck.*module" text))
      (is (not (re-find #"Execution error|Full report at" text))))))

(deftest an-unknown-declaration-is-a-fail-line
  ;; B-20261030-12: "unknown declaration no/such-decl -- name the module..." had no FAIL prefix
  (with-redefs [checkpoint/load-checkpoint (constantly {:status :replayed :environment (environment/empty-environment)})]
    (let [result (atom nil)
          text (with-out-str (reset! result (#'main/show-main ["no/such-decl"])))]
      (is (false? @result))
      (is (re-find #"^FAIL show no/such-decl -- unknown declaration in the default checkpoint -- Check the name, and name the module that installs it" text) text))
    (let [text (with-out-str (#'main/show-main ["no/such-decl" "rainbow.show-errors-test"]))]
      (is (re-find #"^FAIL show no/such-decl -- unknown declaration \(not in the default checkpoint or rainbow.show-errors-test\) -- Check" text) text))))

(defn extend-environment
  "A module that installs nothing, for the unknown-declaration case above."
  [env]
  env)
