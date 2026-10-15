(ns rainbow.term-substitution-test
  "term/shift and term/instantiate skip subterms whose loose-range shows nothing to
  change. These tests compare them with the plain recursive definitions (kept here
  verbatim as the reference) on random open and closed terms."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.term :as term]))

(defn- reference-shift [t delta cutoff]
  (letfn [(walk [node depth]
            (case (first node)
              (:sort :const :nat) node
              :bound (let [i (second node)]
                       (if (>= i (+ cutoff depth))
                         (let [s (+ i delta)]
                           (when (neg? s) (throw (ex-info "escaped" {:error/category :term/invalid-shift})))
                           [:bound s])
                         node))
              :app [:app (walk (second node) depth) (walk (nth node 2) depth)]
              (:lam :pi) [(first node) (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :let [:let (walk (second node) depth) (walk (nth node 2) depth) (walk (nth node 3) (inc depth))]))]
    (walk t 0)))

(defn- reference-instantiate [body argument]
  (letfn [(walk [node depth]
            (case (first node)
              (:sort :const :nat) node
              :bound (let [i (second node)]
                       (cond (= i depth) (reference-shift argument depth 0)
                             (> i depth) [:bound (dec i)]
                             :else node))
              :app [:app (walk (second node) depth) (walk (nth node 2) depth)]
              (:lam :pi) [(first node) (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :let [:let (walk (second node) depth) (walk (nth node 2) depth) (walk (nth node 3) (inc depth))]))]
    (walk body 0)))

(defn- reference-range [t]
  (letfn [(walk [node depth]
            (case (first node)
              (:sort :const :nat) 0
              :bound (if (>= (second node) depth) (inc (- (second node) depth)) 0)
              :app (max (walk (second node) depth) (walk (nth node 2) depth))
              (:lam :pi) (max (walk (second node) depth) (walk (nth node 2) (inc depth)))
              :let (max (walk (second node) depth) (walk (nth node 2) depth) (walk (nth node 3) (inc depth)))))]
    (walk t 0)))

(defn- random-term [^java.util.Random r depth]
  (let [leaf #(case (.nextInt r 4)
                0 [:bound (.nextInt r 5)]
                1 [:const (str "sha256:" (.nextInt r 3)) []]
                2 [:nat (.nextInt r 4)]
                [:sort [:zero]])]
    (if (zero? depth)
      (leaf)
      (case (.nextInt r 5)
        0 (leaf)
        1 [:app (random-term r (dec depth)) (random-term r (dec depth))]
        2 [:lam (random-term r (dec depth)) (random-term r (dec depth)) :explicit]
        3 [:pi (random-term r (dec depth)) (random-term r (dec depth)) :implicit]
        [:let (random-term r (dec depth)) (random-term r (dec depth)) (random-term r (dec depth))]))))

(deftest optimized-substitution-matches-the-reference
  (let [r (java.util.Random. 20261015)]
    (dotimes [_ 4000]
      (let [body (random-term r 5)
            argument (random-term r 4)
            delta (- (.nextInt r 5) 1)
            cutoff (.nextInt r 3)]
        (testing (pr-str body argument)
          (is (= (reference-range body) (term/loose-range body)))
          (is (= (reference-instantiate body argument) (term/instantiate body argument)))
          (let [expected (try (reference-shift body delta cutoff) (catch clojure.lang.ExceptionInfo _ ::escaped))
                actual (try (term/shift body delta cutoff) (catch clojure.lang.ExceptionInfo _ ::escaped))]
            (is (= expected actual))))))))

(deftest a-shared-subterm-keeps-one-range-whatever-its-position
  ;; the cache is keyed by value; the range is a property of the value alone
  (let [open [:app [:bound 2] [:bound 0]]]
    (is (= 3 (term/loose-range open)))
    (is (= 2 (term/loose-range [:lam [:sort [:zero]] open :explicit])))
    (is (= 3 (term/loose-range open)))
    (is (= [:app [:bound 1] [:const "sha256:x" []]]
           (term/instantiate [:app [:bound 2] [:bound 0]] [:const "sha256:x" []])))))
