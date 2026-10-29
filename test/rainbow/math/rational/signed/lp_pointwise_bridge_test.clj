(ns rainbow.math.rational.signed.lp-pointwise-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.math.rational.signed.lp-pointwise-bridge :as pw]))

(defn- fixture [n]
  {:matrix (mapv (fn [i] (mapv #(if (= i %) 1 0) (range n))) (range n))
   :capacities (vec (repeat n 1)) :margins (vec (repeat n 1))
   :plan (vec (repeat n 1/2)) :prices (vec (repeat n 1))})

(defn- elaborate! [env e]
  (let [r (elaborate/core-expression env e)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "LP bridge test expression did not elaborate" {:result r})))
    (:term r)))

(defn- check [env budget spec]
  (let [v (elaborate! env (:value spec))
        t (elaborate! env (:type spec))
        result (binding [kernel/*reduction-budget* budget] (kernel/check env v t #{}))]
    {:status (:status result)
     :error (:error result)
     :axioms (when (= :checked (:status result))
               (into #{} (mapcat #(kernel/axioms env %) (term/constants v))))}))

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "LP bridge checkpoint did not replay" {:status (:status checkpoint)})))
      (pw/extend-environment (:environment checkpoint)))))
(defn- env [] @checked-environment)
(defn- type-rejected? [result]
  (and (= :rejected (:status result))
       (= :kernel/type-mismatch (get-in result [:error :error/category]))))

(deftest pointwise-bridge-uniform-2col
  (let [E (env)
        r (check E 100000 (pw/pointwise-bridge-spec (fixture 2)))]
    (println "PW-UNIFORM-BRIDGE" (pr-str r))
    (is (= :checked (:status r)))
    (is (= #{} (:axioms r)))))

;; validated 3-column signed-nonuniform instance (9ae167c): identity I3,
;; capacities [1 1 1], margins [-1 2 -1], plan [1/2 1 1/2], prices [0 2 0], D=2. Signed and
;; nonuniform, and a genuine LP (its scaled tables match integerize's convention), so the
;; FULL original-bound bridge checks axiom-free -- validating the producer well beyond the
;; 2-col uniform fixture (distinct + negative per-column leaves via the Nat.rec recursion).
(def ^:private signed-3col
  {:matrix [[1 0 0] [0 1 0] [0 0 1]] :capacities [1 1 1]
   :margins [-1 2 -1] :plan [1/2 1 1/2] :prices [0 2 0]})

(deftest pointwise-bridge-signed-nonuniform-3col
  (let [E (env)
        r (check E 100000 (pw/pointwise-bridge-spec signed-3col))]
    (println "PW-3COL-NONUNIFORM" (pr-str r))
    (is (= :checked (:status r)))
    (is (= #{} (:axioms r)))))

(deftest tamper-rejected
  (let [E (env)
        r (check E 100000 (pw/tampered-objective-table (fixture 2)))]
    (println "PW-TAMPER" (pr-str (:status r)))
    (is (type-rejected? r) (pr-str r))))

(deftest last-nonuniform-table-entry-is-checked
  (let [[scaled D] (lp/integerize signed-3col)
        d (#'lp/coefficient-of D)
        sl (update (:margins scaled) 2 inc)
        sr (:plan scaled) ol (:margins signed-3col) oright (:plan signed-3col)
        [left right] (pw/product-maps sl sr ol oright d)
        spec {:type (f/forall [['i lp/nat]]
                             (f/app (f/const* 'signed/equivalent [])
                                    (f/app left 'i) (f/app right 'i)))
              :value (pw/table-product-correspondence sl sr ol oright d)}
        r (check (env) 100000 spec)]
    (is (type-rejected? r) (pr-str r))))

(deftest changed-zero-weight-margin-preserves-the-product
  ;; Rejecting every alteration is not the theorem: the certified relation is
  ;; product equality, and (c+1)*0 = c*0. This must remain an accepted control.
  (let [instance (assoc (fixture 2) :plan [0 1/2])
        r (check (env) 100000 (pw/tampered-objective-table instance))]
    (is (= :checked (:status r)) (pr-str r))
    (is (= #{} (:axioms r)))))

(deftest false-feasibility-premises-cannot-supply-the-bridge
  (doseq [instance [(assoc (fixture 2) :plan [2 1/2])
                    (assoc (fixture 2) :prices [0 1])]]
    (let [r (check (env) 100000 (pw/pointwise-bridge-spec instance))]
      (is (type-rejected? r) (pr-str r)))))

(deftest resource-refusal-cannot-pass-the-tamper-guard
  ;; Mutation of the checker response tests the assertion itself, not a theorem.
  ;; The old not=checked predicate would wrongly accept this injected refusal.
  (let [E (env)
        spec (pw/tampered-objective-table (fixture 2))
        r (with-redefs [kernel/check (fn [& _]
                                      {:status :rejected
                                       :error {:error/category :kernel/resource-limit}})]
            (check E 100000 spec))]
    (is (= :kernel/resource-limit (get-in r [:error :error/category])))
    (is (false? (type-rejected? r)))))
