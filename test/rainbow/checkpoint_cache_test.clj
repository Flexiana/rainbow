(ns rainbow.checkpoint-cache-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]))

(defn- with-cache [read-value replay f]
  ;; Controlled replay outcomes test cache policy, not proof validity. Kernel
  ;; replay is independently covered by the checkpoint and kernel gates.
  (with-redefs-fn {#'checkpoint/replay-cache (atom {})
                  #'checkpoint/read-value read-value
                  #'checkpoint/replay-checkpoint replay}
    f))

(deftest a-resource-limit-does-not-poison-later-replay
  (let [calls (atom 0)]
    (with-cache identity
      (fn [_]
        (swap! calls inc)
        (if (< kernel/*reduction-budget* 100)
          {:status :rejected :error/category :kernel/resource-limit}
          {:status :replayed :environment :checked-fixture}))
      (fn []
        (is (= :rejected (binding [kernel/*reduction-budget* 1]
                          (:status (checkpoint/load-checkpoint "cache-policy-fixture")))))
        (is (= :replayed (binding [kernel/*reduction-budget* 100]
                          (:status (checkpoint/load-checkpoint "cache-policy-fixture")))))
        (is (= 2 @calls))))))

(deftest transient-read-failures-are-retried
  (let [reads (atom 0)]
    (with-cache (fn [_]
                  (if (= 1 (swap! reads inc))
                    (throw (java.io.IOException. "temporary read failure"))
                    :fixture))
      (constantly {:status :replayed :environment :checked-fixture})
      (fn []
        (is (= :rejected (:status (checkpoint/load-checkpoint "read-policy-fixture"))))
        (is (= :replayed (:status (checkpoint/load-checkpoint "read-policy-fixture"))))
        (is (= 2 @reads))))))

(deftest successful-replays-still-share-the-cache
  (let [calls (atom 0)
        success {:status :replayed :environment :checked-fixture}]
    (with-cache identity (fn [_] (swap! calls inc) success)
      (fn []
        (is (= success (checkpoint/load-checkpoint "success-policy-fixture")))
        (is (= success (checkpoint/load-checkpoint "success-policy-fixture")))
        (is (= 1 @calls))))))
