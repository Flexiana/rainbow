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
