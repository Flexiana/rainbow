(ns rainbow.reproduce-errors-test
  "lein reproduce says what to check when a namespace does not exist or is not a milestone
  (B-20261030-11: an unknown namespace printed only the bare \"Could not locate ...\")."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.main :as main]))

(defn- reproduce [& args]
  (let [result (atom nil) text (with-out-str (reset! result (#'main/reproduce-main args)))] [@result text]))

(deftest an-unknown-namespace-says-what-to-check
  (let [[ok text] (reproduce "rainbow.no.such.ns")]
    (is (false? ok))
    (is (re-find #"FAIL +rainbow.no.such.ns -- Could not locate rainbow/no/such/ns" text) text)
    (is (re-find #" -- Check the namespace name \(such as rainbow.milestones.ahof-bisection" text) text)
    (is (= 1 (main/exit-code ok)))))

(deftest a-namespace-that-is-not-a-milestone-names-what-to-give
  (testing "a namespace without run"
    (is (re-find #"not a reproducible milestone .* -- Name a milestone namespace, such as rainbow.milestones.ahof-bisection, or run lein reproduce --all"
                 (:error (main/reproduce-milestone 'clojure.string)))))
  (testing "any other error says the milestone did not rebuild"
    (with-redefs [require (fn [& _] (throw (IllegalStateException. "boom")))]
      (is (= "boom -- The milestone did not rebuild; fix the error above or name another milestone."
             (:error (main/reproduce-milestone 'rainbow.anything)))))))
