(ns rainbow.extension-probe
  "Adversarial child process used to verify the extension sandbox boundary."
  (:require [clojure.edn :as edn])
  (:import (java.net Socket)))

(defn- response [request result]
  {:status :proposed
   :request/id (:request/id request)
   :seed (:seed request)
   :proposals []
   :probe/result result})

(defn -main [& _]
  (let [request (edn/read-string (read-line))
        context (:context request)]
    (case (:mode context)
      :write-outside
      (println
       (pr-str
        (response request
                  (try
                    (spit (:path context) "sandbox escape")
                    :written
                    (catch Throwable _ :denied)))))

      :read-outside
      (println
       (pr-str
        (response request
                  (try
                    (slurp (:path context))
                    :read
                    (catch Throwable _ :denied)))))

      :network
      (println
       (pr-str
        (response request
                  (try
                    (with-open [_ (Socket. "127.0.0.1" (int (:port context)))]
                      :connected)
                    (catch Throwable _ :denied)))))

      :sleep
      (do (Thread/sleep (long (:sleep-ms context)))
          (println (pr-str (response request :woke))))

      :burn
      (let [deadline (+ (System/nanoTime)
                        (* 1000000 (long (:burn-ms context))))]
        (loop [value 0]
          (if (< (System/nanoTime) deadline)
            (recur (unchecked-inc value))
            (println (pr-str (response request value))))))

      :allocate
      (let [bytes (byte-array (* 1024 1024 (long (:memory-mb context))))]
        (println (pr-str (response request (alength bytes)))))

      :fork
      (println
       (pr-str
        (response request
                  (try
                    (let [process (.start (ProcessBuilder. ["/usr/bin/true"]))]
                      (.waitFor process)
                      :forked)
                    (catch Throwable _ :denied)))))

      :oversize
      (println (apply str (repeat 1100000 "x")))

      :malformed
      (println "{not-edn")

      (println (pr-str (response request :ok))))))
