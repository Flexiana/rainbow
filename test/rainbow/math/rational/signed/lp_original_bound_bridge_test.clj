(ns rainbow.math.rational.signed.lp-original-bound-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-original-bound-bridge :as bridge]
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
(defn- expected [original actual endpoint]
  ;; Independent request-based reconstruction, including ORIGINAL constraints.
  (let [z (f/const* 'signed/zero []) truth (f/const* 'proposition/truth [])
        mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
                            (f/lam [['ignored lp/nat]] z)))
        cols (#'lp/index-list (count (:margins original))) rows (#'lp/index-list (count (:capacities actual)))
        sum (fn [m indices] (poly 'signed/map-sum lp/nat m indices))
        dot (fn [a] (sum (f/lam [['j lp/nat]]
                               (app 'signed/multiply (f/app (mapping a) 'j) (f/app 'candidate 'j))) cols))
        clause (fn [relation a b] (app relation (dot a) (#'lp/signed-literal b)))
        clauses (concat (map #(clause 'signed/at-most %1 %2) (:matrix original) (:capacities original))
                        (map #(clause 'signed/equivalent (:row %) (:value %)) (:equalities original)))
        original-constraints (reduce #(app 'proposition/conjunction %2 %1) truth (reverse clauses))
        M (if (seq (:matrix actual))
            (#'lp/nat-lookup (f/arrow lp/nat lp/signed) (mapv mapping (:matrix actual)))
            (f/lam [['ignored lp/nat]] (mapping [])))
        b (mapping (:capacities actual)) c (mapping (:margins actual)) y (mapping (:prices actual))
        zero-on (f/lam [['ignored lp/nat]] z)
        activity (f/lam [['i lp/nat]]
                        (sum (f/lam [['j lp/nat]]
                                    (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app 'candidate 'j))) cols))
        dual (f/lam [['j lp/nat]]
                    (sum (f/lam [['i lp/nat]]
                                (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app y 'i))) rows))
        nn (poly 'signed/all-at-most lp/nat zero-on 'candidate cols)
        OP (app 'proposition/conjunction original-constraints nn)
        AP (app 'proposition/conjunction (poly 'signed/all-at-most lp/nat activity b rows) nn)
        Q (sum (f/lam [['i lp/nat]] (app 'signed/multiply (f/app b 'i) (f/app y 'i))) rows)
        O (dot (:margins original)) S (dot (:margins actual))
        minimum? (= :minimize (:sense original))
        E (#'lp/signed-literal endpoint) SE (#'lp/signed-literal (if minimum? (- endpoint) endpoint))
        cb [['candidate (f/arrow lp/nat lp/signed)]]]
    {:primal-feasibility-equivalence (f/forall cb (app 'proposition/equivalence OP AP))
     :objective-correspondence (f/forall cb (app 'signed/equivalent S (if minimum? (app 'signed/negate O) O)))
     :dual-feasibility (poly 'signed/all-at-most lp/nat c dual cols)
     :dual-nonnegative (poly 'signed/all-at-most lp/nat zero-on y rows)
     :dual-endpoint-bound (app 'signed/at-most Q SE)
     :universal-original-bound
     (f/forall (conj cb ['original-feasible OP])
               (if minimum? (app 'signed/at-most E O) (app 'signed/at-most O E)))}))
(defn- check [label spec target]
  (let [v (core! (:value spec)) t (core! target) r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-ORIGINAL-BOUND" label (pr-str result)) result))
(defn- accepted! [label spec target]
  (let [r (check label spec target)] (is (= :checked (:status r))) (is (= #{} (:axioms r)))))
(defn- rejected! [label spec target]
  (let [r (check label spec target)] (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))
(def ^:private maximum
  {:matrix [[1]] :capacities [2] :margins [1] :plan [0] :prices [0]
   :equalities [{:row [1] :value 1}] :equality-prices [1] :sense :maximize})
(def ^:private minimum (assoc maximum :sense :minimize :equality-prices [-1]))

(deftest both-senses-original-equalities-and-empty-domains
  (doseq [[label original endpoint]
          [[:maximum maximum 1] [:minimum minimum 1]
           [:two-column {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [1 1]
                         :plan [0 0] :prices [1 1] :equalities [{:row [1 -1] :value 0}]
                         :equality-prices [0]} 2]
           [:unconstrained {:matrix [] :capacities [] :margins [0] :plan [0] :prices []} 0]
           [:empty {:matrix [] :capacities [] :margins [] :plan [] :prices []} 0]]]
    (let [actual (#'lp/standard-form original) specs (bridge/original-bound-specs original actual endpoint)
          targets (expected original actual endpoint)]
      (is (= (set (keys targets)) (set (keys specs))))
      (doseq [[kind target] targets] (accepted! [label kind] (get specs kind) target)))))

(deftest loose-endpoints-accepted-and-false-endpoints-rejected
  (doseq [[original loose false-bound] [[maximum 2 0] [minimum 0 2]]]
    (let [actual (#'lp/standard-form original)]
      (doseq [[endpoint valid?] [[loose true] [false-bound false]]]
        (let [specs (bridge/original-bound-specs original actual endpoint) targets (expected original actual endpoint)]
          (doseq [kind [:dual-endpoint-bound :universal-original-bound]]
            ((if valid? accepted! rejected!) [(:sense original) endpoint kind] (get specs kind) (get targets kind))))))))

(deftest objective-negative-price-and-donor-controls
  (doseq [original [maximum minimum]]
    (let [actual (assoc-in (#'lp/standard-form original) [:margins 0] 0)
          specs (bridge/original-bound-specs original actual 1) targets (expected original actual 1)]
      (doseq [kind [:objective-correspondence :universal-original-bound]]
        (rejected! [:wrong-objective (:sense original) kind] (get specs kind) (get targets kind)))))
  ;; Q=1 and dual column=2>=1, but the first price is negative: arithmetic
  ;; endpoint and dual feasibility alone cannot justify weak duality.
  (let [actual (assoc (#'lp/standard-form maximum) :prices [-1 3 0])
        specs (bridge/original-bound-specs maximum actual 1) targets (expected maximum actual 1)]
    (doseq [kind [:dual-feasibility :dual-endpoint-bound]]
      (accepted! [:negative-price kind] (get specs kind) (get targets kind)))
    (doseq [kind [:dual-nonnegative :universal-original-bound]]
      (rejected! [:negative-price kind] (get specs kind) (get targets kind))))
  (let [actual (#'lp/standard-form maximum) donor (bridge/original-bound-specs maximum actual 1)
        receiver (expected (assoc maximum :margins [2]) actual 1)]
    (rejected! :retained-donor (:universal-original-bound donor) (:universal-original-bound receiver))))

(deftest invalid-endpoint-and-price-domain-refused-before-encoding
  (let [actual (#'lp/standard-form maximum)]
    (doseq [bad [0.5 ##NaN 1/10001 18446744073709551616N]]
      (is (= :lp-original-bound/domain
             (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
               #(try (bridge/original-bound-specs maximum actual bad) :unexpected-success
                     (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))
    (is (= :lp-original-bound/domain
           (try (bridge/original-bound-specs maximum (assoc actual :prices [1]) 1) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))
    (is (= :lp-original-bound/sense
           (try (bridge/original-bound-specs (assoc maximum :sense :unsupported) actual 1) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))
