(ns rainbow.math.rational.signed.lp-gap-quality-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.gap-quality :as quality]
            [rainbow.math.rational.signed.lp-gap-quality-bridge :as bridge]
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
(defn- check [label value target]
  (let [v (core! value) t (core! target) r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures)) (into #{} cat closures))}]
    (println "LP-GAP-QUALITY" label (pr-str result)) result))
(defn- accepted! [label value target]
  (let [r (check label value target)] (is (= :checked (:status r))) (is (= #{} (:axioms r)))))
(defn- rejected! [label value target]
  (let [r (check label value target)] (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))
(defn- target [original epsilon]
  ;; Independent receiver construction, using original rows directly. No
  ;; original-bound or quality producer type is consulted.
  (let [zero (f/const* 'signed/zero []) truth (f/const* 'proposition/truth [])
        mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
                            (f/lam [['ignored lp/nat]] zero)))
        cols (#'lp/index-list (count (:margins original)))
        dot (fn [a v] (poly 'signed/map-sum lp/nat
                           (f/lam [['i lp/nat]] (app 'signed/multiply (f/app (mapping a) 'i) (f/app v 'i))) cols))
        feasible (fn [v]
                   (let [clause (fn [rel a b] (app rel (dot a v) (#'lp/signed-literal b)))
                         rows (concat (map #(clause 'signed/at-most %1 %2) (:matrix original) (:capacities original))
                                      (map #(clause 'signed/equivalent (:row %) (:value %)) (:equalities original)))
                         constraints (reduce #(app 'proposition/conjunction %2 %1) truth (reverse rows))]
                     (app 'proposition/conjunction constraints
                          (poly 'signed/all-at-most lp/nat (f/lam [['i lp/nat]] zero) v cols))))
        x (mapping (:plan original)) X (dot (:margins original) x) Y (dot (:margins original) 'candidate)
        difference (if (= :minimize (:sense original)) (app 'signed/subtract X Y) (app 'signed/subtract Y X))]
    (app 'proposition/conjunction (feasible x)
         (f/forall [['candidate (f/arrow lp/nat lp/signed)] ['member (feasible 'candidate)]]
                   (app 'signed/at-most difference (#'lp/signed-literal epsilon))))))

(def ^:private maximum {:matrix [[1]] :capacities [2] :margins [1] :prices [1] :plan [1]})
(def ^:private minimum {:matrix [[-1]] :capacities [-1] :margins [1] :prices [1] :plan [2] :sense :minimize})
(def ^:private upper {:achieved 1 :bound 2 :gap 1 :direction :upper})
(def ^:private lower {:achieved 2 :bound 1 :gap 1 :direction :lower})

(deftest generic-theorems-rechecked-and-axiom-audited
  (doseq [[name id] (quality/theorem-ids @env)]
    (let [d (environment/declaration @env id)
          r (kernel/check @env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))]
      (println "GAP-QUALITY-THEOREM" name id (:status r) (kernel/axioms @env id))
      (is (some? id)) (is (= :checked (:status r))) (is (= #{} (kernel/axioms @env id))))))

(deftest positive-tight-fractional-equality-and-empty-quality
  (doseq [[label original r epsilon]
          [[:upper maximum upper 1] [:lower minimum lower 1]
           [:loose maximum upper 2]
           [:fractional (assoc maximum :plan [3/2]) {:achieved 3/2 :bound 2 :gap 1/2 :direction :upper} 1/2]
           [:zero (assoc maximum :plan [2]) {:achieved 2 :bound 2 :gap 0 :direction :upper} 0]
           [:equality {:matrix [] :capacities [] :margins [1 0] :plan [0 1] :prices []
                       :equalities [{:row [1 1] :value 1}] :equality-prices [1]}
            {:achieved 0 :bound 1 :gap 1 :direction :upper} 1]
           [:empty {:matrix [] :capacities [] :margins [] :plan [] :prices []}
            {:achieved 0 :bound 0 :gap 0 :direction :upper} 0]]]
    (let [specs (bridge/epsilon-specs original (#'lp/standard-form original) r epsilon)]
      (is (= 13 (count specs)))
      (accepted! [label :budget] (:value (:gap-within-budget specs))
                 (app 'signed/at-most (#'lp/signed-literal (:gap r)) (#'lp/signed-literal epsilon)))
      (accepted! [label :quality] (:value (:epsilon-optimal specs)) (target original epsilon)))))

(deftest too-small-budget-false-bound-and-infeasible-plan-rejected
  (doseq [[original r] [[maximum upper] [minimum lower]]]
    (let [specs (bridge/epsilon-specs original (#'lp/standard-form original) r 0)]
      (rejected! :budget (:value (:gap-within-budget specs))
                 (app 'signed/at-most (#'lp/signed-literal 1) (#'lp/signed-literal 0)))
      (rejected! :quality (:value (:epsilon-optimal specs)) (target original 0))))
  (let [specs (bridge/epsilon-specs maximum (#'lp/standard-form maximum)
                                   {:achieved 1 :bound 1 :gap 0 :direction :upper} 0)]
    (rejected! :false-global-bound (:value (:epsilon-optimal specs)) (target maximum 0)))
  (let [original (assoc maximum :plan [-1]) r {:achieved -1 :bound 2 :gap 3 :direction :upper}
        specs (bridge/epsilon-specs original (#'lp/standard-form original) r 3)]
    ;; Improvement at every feasible point <=3 is true, but submitted feasibility
    ;; is false. A quality certificate must NOT silently drop the latter.
    (accepted! :infeasible-budget (:value (:gap-within-budget specs))
               (app 'signed/at-most (#'lp/signed-literal 3) (#'lp/signed-literal 3)))
    (rejected! :infeasible-quality (:value (:epsilon-optimal specs)) (target original 3)))
  (let [specs (bridge/epsilon-specs maximum (#'lp/standard-form maximum) upper 1)]
    (rejected! :donor-tighter-quality (:value (:epsilon-optimal specs)) (target maximum 0))
    (rejected! :donor-changed-plan (:value (:epsilon-optimal specs)) (target (assoc maximum :plan [0]) 1))))

(deftest invalid-epsilon-refused-before-encoding
  (doseq [epsilon [0.5 ##NaN 1/10001 18446744073709551616N]]
    (is (= :lp-gap-quality/domain
           (with-redefs-fn {#'lp/signed-literal (fn [& _] (throw (AssertionError. "Encoder reached")))}
             #(try (bridge/epsilon-specs maximum (#'lp/standard-form maximum) upper epsilon) :unexpected-success
                   (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))))
