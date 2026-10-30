(ns rainbow.or.lp-certificate-shape-test
  "B-20261030-3 and B-20261030-2. certify and bound refuse an instance or certificate of the wrong
  shape -- a plan or price vector of the wrong length, a ragged matrix, an entry that is not an exact
  rational -- before any other work, naming the field; and `lein lp-view` turns every bad input of the
  2026-10-30 nightly E2E (D31-D39) into one FAIL line and exit 1, never a raw exception and never a
  page that calls a malformed certificate certified."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.view.lp :as lp-view]))

(def ^:private env
  (delay (-> (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz"))
             lp-on/extend-environment decide-order/extend-environment)))

;; The E2E instance: maximize 2*x0 - x1 s.t. x0 + x1 <= 4, x0 <= 3; optimum x = (3, 0), y = (0, 2).
(def ^:private instance {:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]})
(def ^:private good (merge instance {:plan [3 0] :prices [0 2]}))

(def ^:private blend
  {:sense :minimize :matrix [[1 0]] :capacities [6] :equalities [{:row [1 1] :value 10}]
   :equality-prices [-5] :margins [2 5] :plan [6 4] :prices [3]})

(defn- refusal [data] (select-keys (lp/shape-problem data) [:error/category :field :expected :actual :entry]))

(deftest well-formed-data-has-no-shape-problem
  (doseq [data [good blend (assoc good :sense :maximize)
                (assoc good :plan '(3 0) :prices [0N 2]) (assoc good :margins [2 -1M] :prices [0 4/2])
                ;; an all-equality instance has no <= rows: empty matrix, capacities and prices
                {:matrix [] :capacities [] :prices [] :margins [1 1] :plan [1 0]
                 :equalities [{:row [1 1] :value 1}] :equality-prices [1]}]]
    (is (nil? (lp/shape-problem data)) (pr-str data))))

(deftest a-vector-of-the-wrong-length-is-refused-naming-the-field
  (doseq [[label data expected]
          [["plan with an extra entry (the E2E certificate [3 0 7])" (assoc good :plan [3 0 7])
            {:field :plan :expected 2 :actual 3}]
           ["short plan" (assoc good :plan [3]) {:field :plan :expected 2 :actual 1}]
           ["missing plan" (dissoc good :plan) {:field :plan :expected 2 :actual :missing}]
           ["prices with an extra entry" (assoc good :prices [0 2 5]) {:field :prices :expected 2 :actual 3}]
           ["short prices" (assoc good :prices [2]) {:field :prices :expected 2 :actual 1}]
           ["missing prices" (dissoc good :prices) {:field :prices :expected 2 :actual :missing}]
           ["matrix with an extra row" (assoc good :matrix [[1 1] [1 0] [0 1]]) {:field :matrix :expected 2 :actual 3}]
           ["capacities with an extra entry" (assoc good :capacities [4 3 9]) {:field :matrix :expected 3 :actual 2}]
           ["missing capacities" (dissoc good :capacities) {:field :capacities :expected 2 :actual :missing}]
           ["margins with an extra entry" (assoc good :margins [2 -1 5]) {:field :matrix :expected 3 :actual 2 :entry [:matrix 0]}]
           ["plan longer than the columns" (assoc good :plan [3 0 0]) {:field :plan :expected 2 :actual 3}]
           ["missing margins (E2E D33)" (dissoc good :margins) {:field :margins :expected :at-least-one :actual :missing}]
           ["ragged matrix" (assoc good :matrix [[1 1] [1]]) {:field :matrix :expected 2 :actual 1 :entry [:matrix 1]}]
           ["matrix row too long" (assoc good :matrix [[1 1 0] [1 0]]) {:field :matrix :expected 2 :actual 3 :entry [:matrix 0]}]
           ["equality row too short" (assoc blend :equalities [{:row [1] :value 10}])
            {:field :equalities :expected 2 :actual 1 :entry [:equalities 0 :row]}]
           ["equality without its free price" (assoc blend :equality-prices [])
            {:field :equality-prices :expected 1 :actual 0}]
           ["free price without an equality" (assoc good :equality-prices [1])
            {:field :equality-prices :expected 0 :actual 1}]]]
    (testing label
      (is (= (assoc expected :error/category :lp-certificate/shape-mismatch) (refusal data))))))

(deftest an-entry-that-is-not-an-exact-rational-is-refused
  (doseq [[label data entry]
          [["keyword in the plan (E2E D38)" (assoc good :plan [:three 0]) [:plan 0]]
           ["string price" (assoc good :prices [0 "2"]) [:prices 1]]
           ["floating-point margin" (assoc good :margins [2 -1.0]) [:margins 1]]
           ["NaN capacity" (assoc good :capacities [##NaN 3]) [:capacities 0]]
           ["nil matrix entry" (assoc good :matrix [[1 1] [nil 0]]) [:matrix 1 0]]
           ["symbolic equality value" (assoc blend :equalities [{:row [1 1] :value 'ten}]) [:equalities 0 :value]]
           ["float in an equality row" (assoc blend :equalities [{:row [1 0.5] :value 10}]) [:equalities 0 :row 1]]
           ["float free price" (assoc blend :equality-prices [-5.0]) [:equality-prices 0]]]]
    (testing label
      (is (= {:error/category :lp-certificate/not-rational :entry entry} (select-keys (refusal data) [:error/category :entry]))))))

(deftest other-malformed-fields-are-refused
  (is (= :lp-certificate/unknown-sense (:error/category (refusal (assoc good :sense :min)))))
  (is (= :lp-certificate/shape-mismatch (:error/category (refusal (assoc good :plan 3)))))
  (is (= :lp-certificate/shape-mismatch (:error/category (refusal (assoc good :matrix [[1 1] 1])))))
  (is (= :lp-certificate/shape-mismatch (:error/category (refusal (assoc blend :equalities [[1 1]])))))
  (is (= :lp-certificate/shape-mismatch (:error/category (refusal [3 0]))))
  (is (= :lp-certificate/empty-instance (:error/category (refusal (assoc good :margins [] :plan [] :matrix [[] []])))))
  (is (= :lp-certificate/empty-instance (:error/category (refusal {:matrix [] :capacities [] :margins [1] :plan [1] :prices []})))))

(deftest certify-and-bound-refuse-a-malformed-certificate-the-kernel-would-have-accepted
  (testing "the well-formed certificate is certified"
    (is (= :certified (:status (lp/certify @env good {:alias 'optimization/shape-good}))))
    (is (= :bounded (:status (lp/bound @env good {:alias 'optimization/shape-good-bound})))))
  (testing "the E2E certificate {:plan [3 0 7]}: the kernel check only reads the first two entries, so it
            used to come back certified naming a three-entry plan"
    (let [bad (assoc good :plan [3 0 7])
          before (with-redefs [lp/shape-problem (constantly nil)]
                   (lp/certify @env bad {:alias 'optimization/shape-unchecked}))
          r (lp/certify @env bad {:alias 'optimization/shape-extra})]
      (is (= :certified (:status before)) "without the check this was certified")
      (is (= [:rejected :lp-certificate/shape-mismatch :plan 2 3]
             ((juxt :status :error/category :field :expected :actual) r)))
      (is (not (contains? r :declarations)) "no declaration is checked or reported")
      (is (= :rejected (:status (lp/bound @env bad {:alias 'optimization/shape-extra-bound}))))))
  (testing "short vectors and non-numbers no longer throw from preflight"
    (doseq [[bad category] [[(assoc good :plan [3]) :lp-certificate/shape-mismatch]
                            [(assoc good :prices [2]) :lp-certificate/shape-mismatch]
                            [(assoc good :plan [:three 0]) :lp-certificate/not-rational]
                            [(dissoc good :margins) :lp-certificate/shape-mismatch]]]
      (doseq [f [#(lp/certify @env bad {:alias 'optimization/shape-short})
                 #(lp/bound @env bad {:alias 'optimization/shape-short-bound})
                 #(lp/bound @env bad {:alias 'optimization/shape-short-scaled :integerize? true})
                 #(lp/certify @env bad {:alias 'optimization/shape-short-reflect :proof :reflection :preflight? false})]]
        (is (= [:rejected category] ((juxt :status :error/category) (f))) (pr-str bad))))))

;; ---- lein lp-view ------------------------------------------------------------

(defn- temp-dir []
  (str (doto (java.io.File/createTempFile "rainbow-lp-view-shape" "") (.delete) (.mkdirs))))

(defn- lp-view
  "Runs lein lp-view's entry point on files holding the given texts; [exit output out-dir-written?]."
  [instance-text certificate-text & flags]
  (let [dir (temp-dir)
        write (fn [name text] (let [f (io/file dir name)] (when text (spit f text)) (str f)))
        out (str (io/file dir "out"))
        code (atom nil)
        output (with-out-str
                 (reset! code (lp-view/run (concat [(write "instance.edn" instance-text)
                                                    (write "certificate.edn" certificate-text) out]
                                                   flags))))]
    [@code output (.exists (io/file out "lp-view.json"))]))

(def ^:private instance-text "{:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]}")

(deftest lp-view-refuses-each-bad-input-with-one-fail-line
  (doseq [[label [instance-text certificate-text & flags] expected]
          [["missing instance file (D31)" [nil "{:plan [3 0] :prices [0 2]}"] "no such file"]
           ["truncated instance (D32)" ["{:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1]" "{:plan [3 0] :prices [0 2]}"]
            "not readable EDN"]
           ["instance without :margins (D33)" ["{:matrix [[1 1] [1 0]] :capacities [4 3]}" "{:plan [3 0] :prices [0 2]}"]
            ":lp-certificate/shape-mismatch"]
           ["three-entry plan (D34)" [instance-text "{:plan [3 0 7] :prices [0 2]}"] ":plan must have 2 entries"]
           ["short prices (D36)" [instance-text "{:plan [3 3] :prices [2]}"] ":prices must have 2 entries"]
           ["short plan (D37)" [instance-text "{:plan [3] :prices [0 2]}"] ":plan must have 2 entries"]
           ["non-numeric plan entry (D38)" [instance-text "{:plan [:three 0] :prices [0 2]}"] ":lp-certificate/not-rational"]
           ["wrong-length margins" ["{:matrix [[1 1] [1 0]] :capacities [4 3] :margins [2 -1 5]}" "{:plan [3 0] :prices [0 2]}"]
            ":lp-certificate/shape-mismatch"]
           ["wrong-length capacities" ["{:matrix [[1 1] [1 0]] :capacities [4]}" "{:plan [3 0] :prices [0 2]}"]
            ":lp-certificate/shape-mismatch"]
           ["ragged matrix" ["{:matrix [[1 1] [1]] :capacities [4 3] :margins [2 -1]}" "{:plan [3 0] :prices [0 2]}"]
            "Row 1 of :matrix must have 2 entries"]
           ["missing certificate file" [instance-text nil] "certificate"]
           ["empty certificate file" [instance-text ""] "not an EDN map"]
           ["certificate that is not a map" [instance-text "[3 0]"] "not an EDN map"]
           ["checkpoint that does not exist (D39)" [instance-text "{:plan [3 0] :prices [0 2]}" "--checkpoint" "artifacts/no/such/checkpoint.edn.gz"]
            "--checkpoint artifacts/no/such/checkpoint.edn.gz"]
           ["--checkpoint without a path" [instance-text "{:plan [3 0] :prices [0 2]}" "--checkpoint"] "no path given"]]]
    (testing label
      (let [[code output written?] (apply lp-view instance-text certificate-text flags)
            lines (remove string/blank? (string/split-lines output))]
        (is (= 1 code))
        (is (= 1 (count lines)) output)
        (is (string/starts-with? (first lines) "FAIL lp-view ") output)
        (is (string/includes? output expected) output)
        (is (= 2 (count (re-seq #" -- " output))) "says what failed and what to check")
        (is (not (re-find #"Exception|Execution error|at rainbow\." output)) output)
        (is (not written?) "nothing is written")))))

(deftest lp-view-still-certifies-and-refuses-as-before
  (let [[code output written?] (lp-view instance-text "{:plan [3 0] :prices [0 2]}")]
    (is (= [0 true] [code written?]))
    (is (string/includes? output "certify: certified 6")))
  (let [[code output written?] (lp-view instance-text "{:plan [3 0] :prices [0 1]}")]
    (is (= [1 true] [code written?]) "a refused certificate is still written, as refused")
    (is (string/includes? output "certify: rejected")))
  (let [[code output] (lp-view instance-text nil)]
    (is (= 1 code))
    (is (string/includes? output "FAIL lp-view certificate"))))
