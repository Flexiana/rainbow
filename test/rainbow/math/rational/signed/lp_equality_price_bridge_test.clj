(ns rainbow.math.rational.signed.lp-equality-price-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-equality-price-bridge :as bridge]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (bridge/extend-environment (:environment r)))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- expected-types [original actual-positive actual-negative]
  ;; Independent target construction: neither producer-supplied :type nor a
  ;; producer helper determines what the receiver asks the kernel to check.
  (let [[p a b] (mapv #'lp/signed-literal [original actual-positive actual-negative])
        z (f/const* 'signed/zero [])]
    {:split (app 'signed/equivalent p (app 'signed/subtract a b))
     :positive-nonnegative (app 'signed/at-most z a)
     :negative-nonnegative (app 'signed/at-most z b)
     :universal-contribution
     (f/forall [['coefficient lp/signed]]
               (app 'signed/equivalent (app 'signed/multiply 'coefficient p)
                    (app 'signed/add (app 'signed/multiply 'coefficient a)
                         (app 'signed/multiply (app 'signed/negate 'coefficient) b))))}))
(defn- check [label spec expected]
  (let [v (core! (:value spec)) t (core! expected)
        r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-EQUALITY-PRICE" label (pr-str result))
    result))
(defn- accepted! [label spec expected]
  (let [r (check label spec expected)]
    (is (= :checked (:status r)))
    (is (= #{} (:axioms r)))))
(defn- rejected! [label spec expected]
  (let [r (check label spec expected)]
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (:category r)))))
(def ^:private instance
  {:matrix [[1]] :capacities [10] :margins [1] :plan [0] :prices [7]
   :equalities [{:row [1] :value 2} {:row [-1] :value -2}
                {:row [2] :value 4} {:row [1/2] :value 1}]
   :equality-prices [2 -3 0 1/2]})

(deftest actual-runtime-prices-against-independent-targets
  (let [actual (:prices (#'lp/standard-form instance))
        bundles (bridge/equality-price-specs (:equality-prices instance) actual 1)]
    (is (= [7 2 0 0 3 0 0 1/2 0] actual))
    (is (= [[1 2] [3 4] [5 6] [7 8]] (mapv :expanded-row-indices bundles)))
    (doseq [{:keys [equality-index expanded-row-indices specs]} bundles]
      (let [[j k] expanded-row-indices
            expected (expected-types (nth (:equality-prices instance) equality-index)
                                     (nth actual j) (nth actual k))]
        (is (= (set (keys expected)) (set (keys specs))))
        (doseq [[label target] expected]
          (is (= (core! target) (core! (:type (get specs label)))))
          (accepted! [equality-index label] (get specs label) target))))))

(deftest mutated-actual-entries-and-retained-proof-controls
  (let [actual (:prices (#'lp/standard-form instance))]
    (doseq [[position value index] [[1 3 0] [8 1 3]]]
      (let [changed (assoc actual position value)
            {:keys [expanded-row-indices specs]}
            (nth (bridge/equality-price-specs (:equality-prices instance) changed 1) index)
            [j k] expanded-row-indices
            expected (expected-types (nth (:equality-prices instance) index)
                                     (nth changed j) (nth changed k))]
        (doseq [label [:split :universal-contribution]]
          (rejected! [position label] (get specs label) (get expected label)))))
    ;; Reusing a valid proof and its self-reported type must not bind a receiver
    ;; to the donor problem. The receiver asks about the changed original p=3.
    (let [donor (bridge/price-pair-specs 2 2 0)
          receiver (expected-types 3 2 0)]
      (doseq [label [:split :universal-contribution]]
        (rejected! [:retained-donor label] (get donor label) (get receiver label))))))

(deftest algebraic-split-alone-is-not-legal-dual-prices
  (let [specs (bridge/price-pair-specs 2 -1 -3)
        expected (expected-types 2 -1 -3)]
    (doseq [label [:split :universal-contribution]]
      (accepted! [:negative-pair label] (get specs label) (get expected label)))
    (doseq [label [:positive-nonnegative :negative-nonnegative]]
      (rejected! [:negative-pair label] (get specs label) (get expected label)))))

(deftest bounded-exact-domain-before-legacy-literal-casts
  (doseq [bad [0.5 ##NaN ##Inf 10001 1/10001 18446744073709551616N]]
    (is (= :lp-equality-price/invalid-scalar
           (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
             #(try (bridge/price-pair-specs bad 0 0) :unexpected-success
                   (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))
  (doseq [[original actual base] [[[1] [1] 0] [[1] [1 0 0] 0]
                                 [[1] [1 0] -1] ['(1) [1 0] 0]
                                 [[] (vec (repeat 33 0)) 33]]]
    (is (= :lp-equality-price/table-shape
           (try (bridge/equality-price-specs original actual base) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
  (is (= [] (bridge/equality-price-specs [] [7] 1))))
