(ns rainbow.math.rational.signed.lp-dual-correspondence-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-dual-correspondence-bridge :as bridge]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (bridge/extend-environment (:environment r)))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- lit [x] (#'lp/signed-literal x))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- targets [original actual]
  ;; Independent reconstruction through runtime dual-price/dual-objective terms,
  ;; with unsplit ORIGINAL equality rows/prices in the original weighted table.
  (let [eqs (:equalities original) base (count (:matrix original))
        free (get original :equality-prices []) z (f/const* 'signed/zero [])
        original-data (assoc original :matrix (into (:matrix original) (map :row eqs))
                             :capacities (into (:capacities original) (map :value eqs))
                             :prices (into (:prices original) free))
        terms (fn [data]
                (if (and (seq (:matrix data)) (seq (:margins data)))
                  (#'lp/instance-terms data)
                  (let [mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv lit xs))
                                            (f/lam [['ignored lp/nat]] z)))
                        y (mapping (:prices data)) b (mapping (:capacities data))
                        rows (#'lp/index-list (count (:capacities data)))
                        weighted (fn [coefficient]
                                   (poly 'signed/map-sum lp/nat
                                         (f/lam [['i lp/nat]] (app 'signed/multiply coefficient (f/app y 'i))) rows))]
                    {:dual-price (f/lam [['column lp/nat]] (weighted z))
                     :dual-objective (weighted (f/app b 'i)) :y y :rows rows})))
        ot (terms original-data) at (terms actual)
        statements (concat
                    (map (fn [i] (app 'signed/equivalent (lit (nth (:prices actual) i)) (lit (nth (:prices original) i)))) (range base))
                    (map (fn [i] (let [j (+ base (* 2 i))]
                                   (app 'signed/equivalent (lit (nth free i))
                                        (app 'signed/subtract (lit (nth (:prices actual) j))
                                             (lit (nth (:prices actual) (inc j))))))) (range (count eqs))))
        conjunction (reduce #(app 'proposition/conjunction %2 %1) (f/const* 'proposition/truth []) (reverse statements))]
    {:price-correspondence conjunction
     :actual-prices-nonnegative (poly 'signed/all-at-most lp/nat (f/lam [['ignored lp/nat]] z) (:y at) (:rows at))
     :dual-columns (f/forall [['column lp/nat]]
                             (app 'signed/equivalent (f/app (:dual-price ot) 'column) (f/app (:dual-price at) 'column)))
     :dual-objective (app 'signed/equivalent (:dual-objective ot) (:dual-objective at))}))
(defn- check [label spec target]
  (let [v (core! (:value spec)) t (core! target) r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-DUAL-CORRESPONDENCE" label (pr-str result)) result))
(defn- accepted! [label spec target]
  (let [r (check label spec target)] (is (= :checked (:status r))) (is (= #{} (:axioms r)))))
(defn- rejected! [label spec target]
  (let [r (check label spec target)] (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))
(def ^:private mixed
  {:matrix [[1 0]] :capacities [2] :prices [1] :margins [0 0] :plan [0 0]
   :equalities [{:row [1 -1] :value 0} {:row [1/2 1] :value 1}] :equality-prices [2 -1]})
(def ^:private equality-only
  {:matrix [] :capacities [] :prices [] :margins [0] :plan [0]
   :equalities [{:row [2] :value 3}] :equality-prices [2]})

(deftest actual-dual-columns-objectives-and-nonminimal-split
  (doseq [[label original replacement-prices]
          [[:mixed mixed nil]
           [:prefix-only {:matrix [[1] [1]] :capacities [1 1] :prices [1 2] :margins [0] :plan [0]} nil]
           [:negative-free (assoc equality-only :equality-prices [-1]) nil]
           [:nonminimal equality-only [5 3]]
           [:zero-column {:matrix [[]] :capacities [2] :prices [3] :margins [] :plan []} nil]
           [:empty {:matrix [] :capacities [] :prices [] :margins [] :plan []} nil]]]
    (let [actual (cond-> (#'lp/standard-form original) replacement-prices (assoc :prices replacement-prices))
          specs (bridge/dual-correspondence-specs original actual) expected (targets original actual)]
      (is (= (set (keys expected)) (set (keys specs))))
      (doseq [[kind target] expected] (accepted! [label kind] (get specs kind) target)))))

(deftest price-coefficient-rhs-and-donor-tampering
  (let [actual (#'lp/standard-form mixed)]
    (doseq [[label changed kinds]
            [[:prefix-price (assoc-in actual [:prices 0] 2) [:price-correspondence :dual-columns :dual-objective]]
             [:free-split (assoc-in actual [:prices 1] 3) [:price-correspondence :dual-columns :dual-objective]]
             [:last-column (assoc-in actual [:matrix 4 1] -2) [:dual-columns]]
             [:rhs (assoc-in actual [:capacities 4] 0) [:dual-objective]]]]
      (let [specs (bridge/dual-correspondence-specs mixed changed) expected (targets mixed changed)]
        (doseq [kind kinds] (rejected! [label kind] (get specs kind) (get expected kind)))))
    (let [donor (bridge/dual-correspondence-specs mixed actual)
          receiver (targets (assoc-in mixed [:equality-prices 1] -2) actual)]
      (doseq [kind [:dual-columns :dual-objective]]
        (rejected! [:retained-donor kind] (get donor kind) (get receiver kind))))))

(deftest algebraic-dual-correspondence-is-not-price-legality
  (let [actual (assoc (#'lp/standard-form equality-only) :prices [-1 -3])
        specs (bridge/dual-correspondence-specs equality-only actual) expected (targets equality-only actual)]
    (doseq [kind [:price-correspondence :dual-columns :dual-objective]]
      (accepted! [:negative-pair kind] (get specs kind) (get expected kind)))
    (rejected! :negative-pair-legality (:actual-prices-nonnegative specs) (:actual-prices-nonnegative expected))))

(deftest zero-column-rhs-still-matters
  ;; Zero columns do NOT imply a zero dual objective: here it changes from 6 to 9.
  (let [original {:matrix [[]] :capacities [2] :prices [3] :margins [] :plan []}
        actual (assoc original :capacities [3])
        specs (bridge/dual-correspondence-specs original actual) expected (targets original actual)]
    (rejected! :zero-column-rhs (:dual-objective specs) (:dual-objective expected))))

(deftest price-shape-and-numeric-refusals-precede-encoding
  (let [actual (#'lp/standard-form mixed)]
    (doseq [original [(assoc mixed :prices []) (assoc mixed :equality-prices [2])]]
      (is (= :lp-dual-correspondence/price-shape
             (try (bridge/dual-correspondence-specs original actual) :unexpected-success
                  (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
    (doseq [bad [0.5 1/10001 18446744073709551616N]]
      (is (= :lp-dual-correspondence/invalid-price
             (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
               #(try (bridge/dual-correspondence-specs (assoc mixed :prices [bad]) actual) :unexpected-success
                     (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))))
