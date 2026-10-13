(ns rainbow.transport-test
  (:require [clojure.test :refer :all]
            [rainbow.history.bool-nat-refinement :as bool-nat-refinement]
            [rainbow.transport :as transport]))

(def built (delay (bool-nat-refinement/build)))
(def live-report (delay (bool-nat-refinement/report)))

(deftest representation-refinement-has-checked-adapters-laws-and-theorems
  (let [report @live-report]
    (is (= :passed (:status report)))
    (is (= :representation-refinement (:relation report)))
    (is (= {:forward :kernel-checked :backward :kernel-checked}
           (:adapters report)))
    (is (= :kernel-checked (get-in report [:laws :source-retraction])))
    (is (= 2 (get-in report [:laws :transported-constructor-theorems])))
    (is (= 5 (:kernel-rechecks report)))
    (is (= #{} (:axioms report)))
    (is (false? (get-in report [:boundary :kernel-rule-added?])))
    (is (= :none (:trusted-base-change report)))))

(deftest transport-validator-rejects-an-adapter-with-the-wrong-direction
  (let [{:keys [environment mapping]} @built
        wrong (assoc mapping :transport/forward (:transport/backward mapping))
        result (transport/validate environment wrong)]
    (is (= :rejected (:status result)))
    (is (= :transport/forward-type (get-in result [:error :error/category])))))

(deftest transport-identity-is-semantic-and-not-status-metadata
  (let [{:keys [mapping checked]} @built]
    (is (= (:transport/id checked) (transport/transport-id mapping)))
    (is (= (:transport/id checked)
           (transport/transport-id
            (assoc mapping :transport/status :unchecked-commentary))))))
