(ns rainbow.elaborate-depth-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.elaborate :as elaborate]))

(def c [:const (str "sha256:" (apply str (repeat 64 "0"))) []])

(defn on-small-stack [f]
  (let [result (promise)
        worker (Thread. nil
                        (fn [] (deliver result (try (f) (catch Throwable e {:thrown (str (class e))}))))
                        "elaboration-regression" 262144)]
    ;; A failed timeout assertion must not leave a non-daemon worker holding the gate open.
    (.setDaemon worker true)
    (.start worker)
    (.join worker 10000)
    (deref result 0 {:timeout true})))

(deftest deeply-nested-applications-do-not-use-the-jvm-call-stack
  (let [depth 3000
        surface (reduce (fn [x _] [:app c x]) [:nat 0] (range depth))
        r (on-small-stack #(elaborate/core-expression {} surface))]
    (is (= :elaborated (:status r)) (pr-str (dissoc r :term)))
    (is (= [depth [:nat 0]]
           (loop [t (:term r) n 0]
             (if (= :app (first t)) (recur (nth t 2) (inc n)) [n t]))))))

(deftest long-binder-lists-preserve-scope
  (let [depth 2000
        bindings (mapv (fn [n] [(symbol (str "x" n)) 'Prop]) (range depth))
        r (on-small-stack #(elaborate/core-expression {} [:fn bindings 'x0]))]
    (is (= :elaborated (:status r)) (pr-str (dissoc r :term)))
    (is (= [depth [:bound (dec depth)]]
           (loop [t (:term r) n 0]
             (if (= :lam (first t)) (recur (nth t 2) (inc n)) [n t]))))))

(deftest mixed-binders-let-and-application-retain-de-bruijn-indices
  (is (= [:lam [:sort [:zero]]
          [:lam [:bound 0]
           [:let [:bound 1] [:bound 0]
            [:app [:lam [:bound 2] [:bound 0] :explicit] [:bound 0]]]
           :explicit] :implicit]
         (:term (elaborate/core-expression {}
                  [:fn [['A 'Prop :implicit] ['x 'A]]
                   [:let 'y 'A 'x [:app [:fn [['z 'A]] 'z] 'y]]]))))
  (is (= [:lam [:sort [:zero]]
          [:pi [:bound 0] [:pi [:bound 1] [:bound 2] :explicit] :explicit]
          :explicit]
         (:term (elaborate/core-expression {} [:fn [['A 'Prop]] [:-> 'A 'A 'A]])))))

(deftest malformed-deep-leaf-still-has-the-original-category
  (let [surface (reduce (fn [x _] [:app c x]) [:nat -1] (range 3000))]
    (is (= :elaborate/invalid-literal
           (get-in (on-small-stack #(elaborate/core-expression {} surface)) [:error :error/category])))))
