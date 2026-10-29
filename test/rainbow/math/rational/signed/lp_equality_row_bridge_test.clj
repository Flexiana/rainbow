(ns rainbow.math.rational.signed.lp-equality-row-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-equality-row-transport :as transport]
            [rainbow.math.rational.signed.lp-equality-row-bridge :as bridge]
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
(defn- expected [original b positive pb negative nb]
  ;; Receiver-owned reconstruction. Producer :type is never the kernel target.
  (let [mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
                            (f/lam [['index lp/nat]] (f/const* 'signed/zero []))))
        [o p n] (mapv mapping [original positive negative])
        [b pb nb] (mapv #'lp/signed-literal [b pb nb])
        eqv (fn [a z] (app 'signed/equivalent a z))
        indices (#'lp/index-list (count original))
        dot (fn [a] (poly 'signed/map-sum lp/nat
                         (f/lam [['i lp/nat]] (app 'signed/multiply (f/app a 'i) (f/app 'candidate 'i))) indices))]
    {:positive-coefficients (f/forall [['index lp/nat]] (eqv (f/app p 'index) (f/app o 'index)))
     :negative-coefficients (f/forall [['index lp/nat]] (eqv (f/app n 'index) (app 'signed/negate (f/app o 'index))))
     :positive-rhs (eqv pb b) :negative-rhs (eqv nb (app 'signed/negate b))
     :feasibility-equivalence
     (f/forall [['candidate (f/arrow lp/nat lp/signed)]]
               (app 'proposition/equivalence (eqv (dot o) b)
                    (app 'proposition/conjunction (app 'signed/at-most (dot p) pb)
                         (app 'signed/at-most (dot n) nb))))}))
(defn- check [label spec target]
  (let [v (core! (:value spec)) t (core! target)
        r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-ACTUAL-ROW" label (pr-str result)) result))
(def ^:private instance
  {:matrix [[1 0]] :capacities [3] :margins [1 1] :plan [0 0] :prices [1]
   :equalities [{:row [2 -3] :value -1} {:row [1/2 1] :value 1/2}]
   :equality-prices [1 -1]})

(deftest generic-transport-is-checked-and-axiom-free
  (doseq [[name id] (transport/theorem-ids @env)]
    (let [d (environment/declaration @env id)
          r (kernel/check @env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))]
      (println "LP-ACTUAL-ROW-THEOREM" name id (:status r) (kernel/axioms @env id))
      (is (some? id)) (is (= :checked (:status r))) (is (= #{} (kernel/axioms @env id))))))

(deftest actual-runtime-rows-and-empty-row
  (let [actual (#'lp/standard-form instance)
        inputs (conj (mapv (fn [i]
                             (let [j (+ 1 (* 2 i)) e (nth (:equalities instance) i)]
                               [(:row e) (:value e) (nth (:matrix actual) j) (nth (:capacities actual) j)
                                (nth (:matrix actual) (inc j)) (nth (:capacities actual) (inc j))])) [0 1])
                     [[] 0 [] 0 [] 0])]
    (doseq [args inputs]
      (let [specs (apply bridge/row-pair-specs args) targets (apply expected args)]
        (is (= (set (keys targets)) (set (keys specs))))
        (doseq [[label target] targets]
          (is (= (core! target) (core! (:type (get specs label)))))
          (let [r (check [(count (first args)) label] (get specs label) target)]
            (is (= :checked (:status r))) (is (= #{} (:axioms r)))))))))

(deftest coefficient-and-rhs-tampering-and-retained-donor
  ;; The submitted plan is [0 0]; changing a coefficient is invisible there.
  ;; These targets quantify every candidate, not just that submitted plan.
  (let [good [[2 -3] -1 [2 -3] -1 [-2 3] 1]]
    (doseq [[args relation] [[(assoc good 2 [3 -3]) :positive-coefficients]
                             [(assoc good 4 [-2 4]) :negative-coefficients]
                             [(assoc good 3 0) :positive-rhs]
                             [(assoc good 5 0) :negative-rhs]]]
      (let [specs (apply bridge/row-pair-specs args) targets (apply expected args)]
        (doseq [label [relation :feasibility-equivalence]]
          (let [r (check [:tamper label] (get specs label) (get targets label))]
            (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r)))))))
    (let [donor (apply bridge/row-pair-specs good)
          targets (apply expected (assoc good 1 0))
          r (check :retained-donor (:feasibility-equivalence donor) (:feasibility-equivalence targets))]
      (is (= :rejected (:status r))) (is (= :kernel/type-mismatch (:category r))))))

(deftest malformed-rows-refused-before-encoding
  (doseq [args [[[1] 0 [] 0 [-1] 0] [(vec (repeat 33 0)) 0 (vec (repeat 33 0)) 0 (vec (repeat 33 0)) 0]]]
    (is (= :lp-equality-row/table-shape
           (try (apply bridge/row-pair-specs args) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
  (doseq [bad [0.5 ##NaN 10001 1/10001 18446744073709551616N]]
    (is (= :lp-equality-row/invalid-scalar
           (with-redefs-fn {#'lp/signed-literal (fn [_] (throw (ex-info "Encoder reached" {})))}
             #(try (bridge/row-pair-specs [1] 0 [1] bad [-1] 0) :unexpected-success
                   (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))))
