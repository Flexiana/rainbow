(ns rainbow.math.rational.signed.lp-plan-report-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-original-bound-bridge-test :as bound-test]
            [rainbow.math.rational.signed.lp-plan-report-bridge :as bridge]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (bridge/extend-environment (:environment r)))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- targets [original actual report optimal?]
  ;; Reuse the independent RECEIVER target builder, never the proof producer.
  (let [base (#'bound-test/expected original actual (:bound report))
        bindings (second (:universal-original-bound base))
        OP (second (second bindings))
        z (f/const* 'signed/zero [])
        mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
                            (f/lam [['ignored lp/nat]] z)))
        x (mapping (:plan original)) c (mapping (:margins original))
        cols (#'lp/index-list (count (:margins original)))
        obj (fn [v] (poly 'signed/map-sum lp/nat
                         (f/lam [['i lp/nat]] (app 'signed/multiply (f/app c 'i) (f/app v 'i))) cols))
        PX (f/app (f/lam [(first bindings)] OP) x)
        [A B G] (mapv #'lp/signed-literal ((juxt :achieved :bound :gap) report))
        minimum? (= :minimize (:sense original))
        expected (assoc base
                        :submitted-plan-feasible PX
                        :achieved-value (app 'signed/equivalent (obj x) A)
                        :reported-gap (app 'signed/equivalent (if minimum? A B)
                                           (app 'signed/add (if minimum? B A) G))
                        :gap-nonnegative (app 'signed/at-most z G)
                        :reported-order (if minimum? (app 'signed/at-most B A) (app 'signed/at-most A B)))]
    (if-not optimal? expected
      (assoc expected :tight-endpoint (app 'signed/equivalent A B)
             :optimality (app 'proposition/conjunction PX
                              (f/forall bindings
                                        (if minimum? (app 'signed/at-most (obj x) (obj 'candidate))
                                            (app 'signed/at-most (obj 'candidate) (obj x)))))))))
(defn- check [label spec target]
  (let [v (core! (:value spec)) t (core! target) r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-PLAN-REPORT" label (pr-str result)) result))
(defn- accepted! [label spec target]
  (let [r (check label spec target)] (is (= :checked (:status r))) (is (= #{} (:axioms r)))))
(defn- rejected! [label spec target]
  (let [r (check label spec target)] (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))
(def ^:private maximum {:matrix [[1]] :capacities [2] :margins [1] :prices [1] :plan [2]})
(def ^:private minimum {:matrix [[-1]] :capacities [-1] :margins [1] :prices [1] :plan [1] :sense :minimize})
(def ^:private equality
  {:matrix [] :capacities [] :margins [1 1] :prices [] :plan [1 0]
   :equalities [{:row [1 1] :value 1}] :equality-prices [1]})
(defn- report [a b g direction] {:achieved a :bound b :gap g :direction direction})

(deftest complete-original-plan-report-and-optimality
  (doseq [[label original r]
          [[:maximum maximum (report 2 2 0 :upper)] [:minimum minimum (report 1 1 0 :lower)]
           [:equality equality (report 1 1 0 :upper)]
           [:empty {:matrix [] :capacities [] :margins [] :prices [] :plan []} (report 0 0 0 :upper)]]]
    (let [actual (#'lp/standard-form original) specs (bridge/optimality-specs original actual r)
          expected (targets original actual r true)]
      (is (= (set (keys expected)) (set (keys specs))))
      (doseq [[kind target] expected] (accepted! [label kind] (get specs kind) target)))))

(deftest nonoptimal-feasible-plans-have-valid-positive-gap-reports
  (doseq [[original r] [[(assoc maximum :plan [1]) (report 1 2 1 :upper)]
                        [(assoc minimum :plan [2]) (report 2 1 1 :lower)]]]
    (let [actual (#'lp/standard-form original) specs (bridge/plan-report-specs original actual r)
          expected (targets original actual r false)
          optional (bridge/optimality-specs original actual r)
          opt-targets (targets original actual r true)]
      (doseq [[kind target] expected] (accepted! [:positive-gap kind] (get specs kind) target))
      (doseq [kind [:tight-endpoint :optimality]]
        (rejected! [:not-tight kind] (get optional kind) (get opt-targets kind))))))

(deftest report-feasibility-zero-gap-and-donor-controls
  (let [actual (#'lp/standard-form maximum) r (report 1 2 1 :upper)
        specs (bridge/plan-report-specs maximum actual r) expected (targets maximum actual r false)]
    (accepted! :scalar-gap-alone (:reported-gap specs) (:reported-gap expected))
    (doseq [kind [:achieved-value :reported-order]]
      (rejected! [:wrong-achieved kind] (get specs kind) (get expected kind))))
  (doseq [g [1 -1]]
    (let [actual (#'lp/standard-form maximum) r (report 2 2 g :upper)
          specs (bridge/plan-report-specs maximum actual r) expected (targets maximum actual r false)]
      (rejected! [:wrong-gap g] (:reported-gap specs) (:reported-gap expected))
      (when (neg? g) (rejected! :negative-gap (:gap-nonnegative specs) (:gap-nonnegative expected)))))
  (let [original (assoc equality :plan [2 -1]) actual (#'lp/standard-form original) r (report 1 1 0 :upper)
        specs (bridge/optimality-specs original actual r) expected (targets original actual r true)]
    ;; Equality, cost, endpoint and universal bound are valid; the plan is illegal.
    (doseq [kind [:universal-original-bound :achieved-value :tight-endpoint]]
      (accepted! [:negative-plan kind] (get specs kind) (get expected kind)))
    (doseq [kind [:submitted-plan-feasible :optimality]]
      (rejected! [:negative-plan kind] (get specs kind) (get expected kind))))
  (let [original (assoc maximum :plan [1]) actual (#'lp/standard-form original)
        r (report 1 2 0 :upper) specs (bridge/optimality-specs original actual r)
        expected (targets original actual r true)]
    (doseq [kind [:reported-gap :tight-endpoint :optimality]]
      (rejected! [:forged-zero-gap kind] (get specs kind) (get expected kind))))
  (let [actual (#'lp/standard-form maximum)
        donor (bridge/optimality-specs maximum actual (report 2 2 0 :upper))
        receiver (targets (assoc maximum :plan [1]) actual (report 1 2 1 :upper) true)]
    (rejected! :retained-plan-donor (:optimality donor) (:optimality receiver))))

(deftest exact-report-and-plan-domain-precede-encoding
  (let [actual (#'lp/standard-form maximum) good (report 2 2 0 :upper)]
    (doseq [[original r] [[maximum (assoc good :direction :lower)] [maximum (assoc good :achieved 2.0)]
                          [maximum (assoc good :gap 1/10001)] [maximum (assoc good :status :optimal)]
                          [(assoc maximum :plan [2 2]) good]
                          [(assoc maximum :plan [18446744073709551616N]) good]]]
      (is (= :lp-plan-report/domain
             (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
               #(try (bridge/plan-report-specs original actual r) :unexpected-success
                     (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))))
