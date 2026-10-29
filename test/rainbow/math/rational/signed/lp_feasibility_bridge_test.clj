(ns rainbow.math.rational.signed.lp-feasibility-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-feasibility-bridge :as bridge]
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
(defn- targets [original actual]
  ;; Independent receiver: normal nonempty expanded targets use the unchanged
  ;; runtime's instance-terms, not any producer target or assembly helper.
  (let [n (count (:margins original)) cols (#'lp/index-list n)
        zero (f/const* 'signed/zero []) truth (f/const* 'proposition/truth [])
        constraint (fn [relation coefficients rhs]
                     (let [m (if (seq coefficients)
                               (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal coefficients))
                               (f/lam [['ignored lp/nat]] zero))]
                       (app relation
                            (poly 'signed/map-sum lp/nat
                                  (f/lam [['j lp/nat]]
                                         (app 'signed/multiply (f/app m 'j) (f/app 'candidate 'j))) cols)
                            (#'lp/signed-literal rhs))))
        clauses (concat (map #(constraint 'signed/at-most %1 %2) (:matrix original) (:capacities original))
                        (map #(constraint 'signed/equivalent (:row %) (:value %)) (:equalities original)))
        O (reduce #(app 'proposition/conjunction %2 %1) truth (reverse clauses))
        A (if (and (pos? n) (seq (:matrix actual)))
            (let [t (#'lp/instance-terms actual)]
              (poly 'signed/all-at-most lp/nat ((:row-activity t) 'candidate) (:b t) (:rows t)))
            ;; Zero-column rows have exactly zero activity; an empty row list
            ;; imposes truth. These are explicit empty-domain extensions.
            (reduce #(app 'proposition/conjunction %2 %1) truth
                    (reverse (map #(app 'signed/at-most zero (#'lp/signed-literal %)) (:capacities actual)))))
        nn (poly 'signed/all-at-most lp/nat (f/lam [['ignored lp/nat]] zero) 'candidate cols)
        cb [['candidate (f/arrow lp/nat lp/signed)]]]
    {:constraints-equivalence (f/forall cb (app 'proposition/equivalence O A))
     :primal-feasibility-equivalence
     (f/forall cb (app 'proposition/equivalence (app 'proposition/conjunction O nn)
                      (app 'proposition/conjunction A nn)))}))
(defn- check [label spec expected]
  (let [v (core! (:value spec)) t (core! expected)
        r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-WHOLE-FEASIBILITY" label (pr-str result)) result))
(def ^:private mixed
  {:matrix [[1 0]] :capacities [3] :margins [1 1] :plan [0 0] :prices [1]
   :equalities [{:row [2 -1] :value 1}] :equality-prices [1]})

(deftest actual-whole-problem-mixed-and-degenerate-domains
  (doseq [[label original]
          [[:mixed mixed]
           [:inequalities-only {:matrix [[1]] :capacities [1] :margins [1] :plan [0] :prices [1]}]
           [:equalities-only {:matrix [] :capacities [] :margins [1] :plan [0] :prices []
                              :equalities [{:row [1] :value 2}] :equality-prices [1]}]
           [:empty {:matrix [] :capacities [] :margins [] :plan [] :prices []}]
           [:zero-column {:matrix [[]] :capacities [0] :margins [] :plan [] :prices [0]}]]]
    (let [actual (#'lp/standard-form original) expected (targets original actual)
          specs (bridge/feasibility-specs original actual)]
      (is (= (set (keys expected)) (set (keys specs))))
      (doseq [[kind target] expected]
        (let [r (check [label kind] (get specs kind) target)]
          (is (= :checked (:status r))) (is (= #{} (:axioms r))))))))

(deftest prefix-equality-and-donor-tampering
  (let [actual (#'lp/standard-form mixed)]
    (doseq [[label changed] [[:prefix-coefficient (assoc-in actual [:matrix 0 0] 2)]
                             [:prefix-rhs (assoc-in actual [:capacities 0] 4)]
                             [:equality-negative-coefficient (assoc-in actual [:matrix 2 1] 2)]
                             [:equality-negative-rhs (assoc-in actual [:capacities 2] 0)]]]
      (let [expected (targets mixed changed) specs (bridge/feasibility-specs mixed changed)]
        (doseq [[kind target] expected]
          (let [r (check [label kind] (get specs kind) target)]
            (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))))
    (let [donor (bridge/feasibility-specs mixed actual)
          receiver (targets (assoc-in mixed [:equalities 0 :value] 2) actual)]
      (doseq [[kind target] receiver]
        (let [r (check [:retained-donor kind] (get donor kind) target)]
          (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r))))))))

(deftest exact-row-count-and-pre-encoding-refusals
  (let [actual (#'lp/standard-form mixed)]
    (doseq [changed [(-> actual (update :matrix pop) (update :capacities pop))
                     (-> actual (update :matrix conj [0 0]) (update :capacities conj 0))]]
      (is (= :lp-feasibility/table-shape
             (try (bridge/feasibility-specs mixed changed) :unexpected-success
                  (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
    (doseq [bad [0.5 1/10001 18446744073709551616N]]
      (is (= :lp-feasibility/invalid-scalar
             (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
               #(try (bridge/feasibility-specs mixed (assoc-in actual [:matrix 0 0] bad)) :unexpected-success
                     (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))))
