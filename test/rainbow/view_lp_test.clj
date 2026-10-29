(ns rainbow.view-lp-test
  "The LP Certificate Viewer (lein lp-view) gives rainbow.or.lp-certificate's own verdicts, every step
  of an accepted certificate is kernel-checked, negative controls are refused, and a tampered
  certificate is refused in the written page."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.view :as view]
            [rainbow.view.lp :as lp-view]))

(def ^:private env (delay (lp-view/environment)))

(def ^:private penalty-mix {:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]})
(def ^:private penalty-certificate {:plan [3 0] :prices [0 2]})

(defn- verdicts [instance certificate]
  (let [data (lp-view/view-data @env instance certificate)
        e (first (:examples data))]
    [(:status (lp/certify @env (merge instance certificate))) (get-in e [:certify :status]) e]))

(defn- kernel-marks [steps]
  (for [x (tree-seq coll? seq (dissoc steps :controls)) :when (and (map? x) (:kernel x))] (:kernel x)))

(deftest lp-view-agrees-with-the-certificate-checker
  (doseq [[label instance certificate expected]
          [["optimal, with a penalty" penalty-mix penalty-certificate :certified]
           ["fractional dual price" {:matrix [[1 1 1] [2 0 0] [0 1 0]] :capacities [10 8 5] :margins [3 1 -2]} {:plan [4 5 0] :prices [0 3/2 1]} :certified]
           ["cost problem" {:sense :minimize :matrix [[-1 -1]] :capacities [-4] :margins [2 3]} {:plan [4 0] :prices [2]} :certified]
           ["equality row with a free price" {:sense :minimize :matrix [[1 0]] :capacities [6] :equalities [{:row [1 1] :value 10}] :margins [2 5]}
            {:plan [6 4] :prices [3] :equality-prices [-5]} :certified]
           ["suboptimal plan" penalty-mix {:plan [2 0] :prices [0 2]} :rejected]
           ["infeasible plan" penalty-mix {:plan [5 0] :prices [0 2]} :rejected]]]
    (testing label
      (let [[direct viewed e] (verdicts instance certificate)]
        (is (= expected direct viewed))
        (when (= :certified expected)
          (is (every? #{:checked} (kernel-marks (:steps e))) "every step of an accepted certificate is kernel-checked")
          (is (every? empty? (map :axioms (get-in e [:certify :declarations])))))
        (is (every? #(= :rejected (:kernel %)) (vals (get-in e [:steps :controls]))) "negative controls are refused")))))

(deftest a-tampered-certificate-is-refused-in-the-written-page
  (let [dir (str (doto (java.io.File/createTempFile "rainbow-lp-view" "") (.delete)))
        tampered {:plan [3 0] :prices [0 1]}                ; the price of row 2 lowered from 2 to 1
        data (lp-view/view-data @env penalty-mix tampered)
        _ (view/write-page! dir "scripts/lp-view.html" "lp-view.json" data false)
        text (slurp (io/file dir "lp-view.json"))
        e (first (:examples data))]
    (is (= :rejected (get-in e [:certify :status]) (:status (lp/certify @env (merge penalty-mix tampered)))))
    (is (some? (get-in e [:certify :kernel-category])))
    (testing "the step that fails is named: the prices no longer cover the margin of x1, and the gap is open"
      (is (= [:rejected :checked] (map #(get-in % [:covers-margin :kernel]) (get-in e [:steps :columns]))))
      (is (= :rejected (get-in e [:steps :objectives-equal :kernel])))
      (is (= "-3" (get-in e [:steps :gap]))))
    (testing "the written files carry the refusal, the page inline"
      (is (= (view/json data) text))
      (is (string/includes? text "\"status\":\"rejected\""))
      (is (= text (second (re-find #"(?s)<script id=\"rainbow-data\" type=\"application/json\">(.*?)</script>"
                                   (slurp (io/file dir "index.html")))))))))
