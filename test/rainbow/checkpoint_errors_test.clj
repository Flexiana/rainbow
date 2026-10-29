(ns rainbow.checkpoint-errors-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.main :as main]
            [rainbow.checkpoint :as checkpoint]))

(def unreadable {:status :rejected :message "No such file: absent.edn.gz"
                 :error/category :day54/checkpoint-read-failed})

(deftest namespace-command-retains-checkpoint-read-cause
  (with-redefs [checkpoint/load-checkpoint (constantly unreadable)]
    (let [result (atom nil)
          text (with-out-str (reset! result (#'main/verify-namespace-main ["--checkpoint" "absent.edn.gz" "rainbow.unused"])))]
      (is (false? @result))
      (is (re-find #"checkpoint-read-failed" text))
      (is (re-find #"No such file" text))
      (is (re-find #"[Cc]heck" text)))))

(deftest bundle-check-retains-checkpoint-read-cause
  (with-redefs [checkpoint/load-checkpoint (constantly unreadable)]
    (let [r (main/check-bundle {:rainbow.bundle/schema-version 1
                               :claims {'x {:id "unused"}} :declarations []
                               :base {:checkpoint "absent.edn.gz"}})]
      (is (false? (:ok? r)))
      (is (= :day54/checkpoint-read-failed (:error/category r)))
      (is (re-find #"No such file" (:error r))))))

(deftest replay-rejections-are-not-described-as-missing-files
  (let [text (#'main/checkpoint-failure-message "bad.edn.gz"
               {:status :rejected :error/category :day54/checkpoint-id-mismatch})]
    (is (re-find #"checkpoint-id-mismatch" text))
    (is (re-find #"compatible" text))
    (is (not (re-find #"path exists" text)))))
