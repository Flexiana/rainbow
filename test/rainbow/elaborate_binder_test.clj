(ns rainbow.elaborate-binder-test
  "A binder whose name is not a symbol is rejected as a malformed form; there is no separate
  invalid-binder category."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.elaborate :as elaborate]))

(deftest a-non-symbol-binder-name-is-a-malformed-form
  (is (= :elaborate/invalid-forall
         (get-in (elaborate/type-expression [:forall [[1 'Prop]] 'Prop]) [:error :error/category])))
  (is (= :elaborate/invalid-lambda
         (get-in (elaborate/core-expression {} [:fn [["x" 'Prop]] 'Prop]) [:error :error/category])))
  (is (= :elaborated (:status (elaborate/type-expression [:forall [['p 'Prop]] 'p])))))
