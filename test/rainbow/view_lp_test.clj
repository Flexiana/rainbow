(ns rainbow.view-lp-test
  "The LP Certificate Viewer (lein lp-view) gives rainbow.or.lp-certificate's own verdicts, every step
  of an accepted certificate is kernel-checked, negative controls are refused, and a tampered
  certificate is refused in the written page."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
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

(deftest the-page-text-for-an-instance-without-labels
  ;; B-20261030-4: the minimal instance (no :variables) printed the legend "x1 = ; x2 = ."; a
  ;; :variables list shorter than the columns, or an entry without :label, broke the page
  (testing "every column gets a name and a string label, in order"
    (is (= [{:name "x1" :label ""} {:name "x2" :label ""}] (lp-view/page-variables nil 2)))
    (is (= [{:name "chairs" :label ""} {:name "x2" :label ""}] (lp-view/page-variables [{:name "chairs"}] 2)))
    (is (= [{:name "x1" :label "tables"} {:name "x2" :label ""}] (lp-view/page-variables [{:label "tables"} "junk" {:name "x3"}] 2)))
    (is (= ["Row 1" "Row 2"] (lp-view/page-constraints nil 2)))
    (is (= ["wood" "Row 2" "Row 3"] (lp-view/page-constraints ["wood"] 3)))
    (is (= ["wood" "nails"] (lp-view/page-constraints ["wood" "nails" "glue"] 2))))
  (testing "the viewer's data for the minimal instance carries empty labels, and the page lists none of them"
    (let [e (first (:examples (lp-view/view-data @env penalty-mix penalty-certificate)))
          html (slurp "scripts/lp-view.html")]
      (is (= [{:name "x1" :label ""} {:name "x2" :label ""}] (:variables e)))
      (is (= ["Row 1" "Row 2"] (:constraints e)))
      (is (string/includes? html "e.variables.filter(function (x) { return x.label && String(x.label).trim(); })"))
      (is (string/includes? html "(legend ? legend + \". \" : \"\")"))))
  (testing "the paragraph under the program reads \"an “at least” row\""
    (let [html (slurp "scripts/lp-view.html")]
      (is (string/includes? html "an “at least” row is negated"))
      (is (not (string/includes? html "a “at least”"))))))

(defn- js-array [strings] (str "[" (string/join ", " (map pr-str strings)) "]"))

(defn- page-linform
  "The page's own linform (scripts/lp-view.html) run by node on coefficients and names, or nil when
  node is not installed."
  [coeffs names]
  (let [html (slurp "scripts/lp-view.html")
        start (string/index-of html "  function parts(s) {")
        end (string/index-of html "  // a written-out evaluation")
        source (str (subs html start end)
                    "process.stdout.write(linform(" (js-array coeffs) ", " (js-array names) "));")]
    (try (let [{:keys [exit out err]} (shell/sh "node" "-e" source)]
           (is (zero? exit) err)
           out)
         (catch java.io.IOException _ nil))))

(deftest a-coefficient-does-not-run-into-a-multi-letter-name
  ;; B-20261030-6: the program read "2chairs − x2"; a longer name gets a dot, a one-letter one does not
  (let [html (slurp "scripts/lp-view.html")]
    (is (string/includes? html "+ times(mag, vars[j])"))
    (is (not (string/includes? html "mag + v(vars[j])"))))
  (when-let [out (page-linform ["2" "-1" "3/2"] ["chairs" "x2" "tables"])]
    (is (= (str "2·<var class=\"v\">chairs</var>"
                " − <var class=\"v\">x<sub>2</sub></var>"
                " + <span class=\"frac\" aria-label=\"3 over 2\"><span>3</span><span>2</span></span>·<var class=\"v\">tables</var>")
           out)))
  (when-let [out (page-linform ["2" "1" "-5"] ["x1" "chairs" "y"])]
    (is (= (str "2<var class=\"v\">x<sub>1</sub></var>"
                " + <var class=\"v\">chairs</var>"
                " − 5<var class=\"v\">y</var>")
           out))))
