(ns rainbow.canonical-encoding-test
  "canonical/encode writes through one StringBuilder. Content ids are hashes of this
  encoding, so it must be byte-identical to the original string-concatenating
  definition, kept verbatim in rainbow.canonical-reference."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.canonical :as canonical]
            [rainbow.canonical-stream :as canonical-stream]
            [rainbow.canonical-reference :as reference]
            [rainbow.term :as term]))

(defn- random-value [^java.util.Random r depth]
  (let [leaf #(case (.nextInt r 10)
                0 nil 1 true 2 false
                3 (apply str (repeatedly (.nextInt r 6) (fn [] (char (+ 97 (.nextInt r 26))))))
                4 (keyword (str "k" (.nextInt r 5)))
                5 (keyword (str "ns" (.nextInt r 3)) (str "k" (.nextInt r 5)))
                6 (symbol (str "ns" (.nextInt r 3)) (str "s" (.nextInt r 5)))
                7 (- (.nextInt r 1000) 500)
                8 (bigint (str (.nextInt r 1000) "123456789012345678901234567890"))
                (/ (inc (.nextInt r 50)) (+ 2 (.nextInt r 50))))]
    (if (zero? depth)
      (leaf)
      (case (.nextInt r 6)
        0 (leaf)
        1 (vec (repeatedly (.nextInt r 4) #(random-value r (dec depth))))
        2 (apply list (repeatedly (.nextInt r 4) #(random-value r (dec depth))))
        3 (set (repeatedly (.nextInt r 4) #(random-value r (dec depth))))
        (into {} (repeatedly (.nextInt r 4) #(vector (random-value r 0) (random-value r (dec depth)))))))))

(deftest encoding-is-byte-identical-to-the-reference
  (let [r (java.util.Random. 20261015)]
    (dotimes [_ 3000]
      (let [v (random-value r 4)]
        (is (= (reference/encode v) (canonical/encode v)) (pr-str v))))))

(deftest incremental-hashing-preserves-legacy-identities
  (let [r (java.util.Random. 20261024)
        high (str (char 0xd800))
        low (str (char 0xdc00))
        unicode [high low (str high low) (str low high) "é漢字"
                 (str (apply str (repeat 8190 "x")) high low)]]
    (doseq [v (concat [nil true false 0 -19 1/3 999999999999999999999999N
                      [] '() #{} {} #{[1 2] '(3 4)}
                      {[:key 1] #{:x 'y "z"}}]
                     unicode (mapv vector unicode)
                     (repeatedly 3000 #(random-value r 4)))]
      (is (= (canonical/sha256 (reference/encode v))
             (canonical-stream/content-id-incremental v)) (pr-str v))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported value"
                       (canonical-stream/content-id-incremental 1.25))))

(deftest universe-instantiation-matches-the-reference
  ;; with no universe arguments, unfolding still normalizes levels, now once per body
  (let [levels [[:zero] [:succ [:zero]] [:max [:zero] [:succ [:zero]]] [:imax [:succ [:zero]] [:zero]]
                [:param 'u] [:max [:param 'u] [:param 'u]]]
        r (java.util.Random. 7)
        pick #(nth levels (.nextInt r (count levels)))
        reference (fn walk [t s]
                    (case (first t)
                      :sort [:sort (term/instantiate-level (second t) s)]
                      (:bound :nat) t
                      :const [:const (second t) (mapv #(term/instantiate-level % s) (nth t 2))]
                      :app [:app (walk (second t) s) (walk (nth t 2) s)]
                      (:lam :pi) [(first t) (walk (second t) s) (walk (nth t 2) s) (nth t 3)]
                      :let [:let (walk (second t) s) (walk (nth t 2) s) (walk (nth t 3) s)]))
        random (fn random [d] (if (zero? d)
                                (case (.nextInt r 3) 0 [:sort (pick)] 1 [:const "sha256:a" [(pick) (pick)]] [:bound 0])
                                (case (.nextInt r 3) 0 [:app (random (dec d)) (random (dec d))]
                                                     1 [:pi (random (dec d)) (random (dec d)) :explicit]
                                                     (random 0))))]
    (dotimes [_ 1000]
      (let [t (random 4)]
        (is (= (reference t {}) (term/instantiate-universes t {})))
        (is (= (reference t {}) (term/instantiate-universes t {}))) ; second call: from the cache
        (is (= (reference t {'u [:succ [:zero]]}) (term/instantiate-universes t {'u [:succ [:zero]]})))))))
