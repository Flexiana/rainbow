(ns rainbow.math.finite.markov-coupling-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-coupling-distance :as target]))
(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        _ (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))]
    (target/extend-environment (:environment cp)))))
(deftest off-diagonal-coupling-bound-is-kernel-checked
  (let [env @checked-environment]
    (doseq [[name id] (target/theorem-ids env)]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))

(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def nat (c 'data/Nat))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- rational [n] (app 'nnrat/make (numeral n) (numeral 0)))
(defn- choose [type first-value later-value]
  (f/lam [['n nat]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
           (f/lam [['ignored nat]] type) first-value
           (f/lam [['previous nat] ['acc type]] later-value) 'n)))
(defn- equivalent-proof [a b]
  (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat
         (app 'nat/multiply (app 'nnrat/numerator a) (app 'nnrat/denominator b))))
(defn- core [env surface]
  (let [r (elaborate/core-expression env surface)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Example elaboration failed" r)))
    (:term r)))
(defn- off-diagonal-example [identical? expected-left expected-right]
  (let [env @checked-environment
        zero (rational 0) one (rational 1)
        left (choose nnrat one zero) right (choose nnrat zero one)
        transition (choose (f/arrow nat nnrat) left (if identical? left right))
        states (app 'finset-data/range (numeral 2))
        total (fn [m] (poly 'probability/nnrat-total-mass nat states m))
        p (f/lam [['i nat]] (app 'nnrat/left-residual-mass (f/app left 'i) (f/app right 'i)))
        proof (poly 'markov/nnrat-kernel-step-positive-residual-coupling-bound
                    nat states left right transition (numeral 0) (numeral 0)
                    (equivalent-proof (total left) (total right))
                    (equivalent-proof (total p) one))
        statement (app 'nnrat/at-most (rational expected-left) (rational expected-right))]
    (kernel/check env (core env proof) (core env statement) #{})))

(deftest off-diagonal-pairing-detects-identical-and-disjoint-rows
  ;; With disjoint residual masses, identical rows have row-pair cost 0;
  ;; the old same-source upper bound was 2 for precisely this example.
  (is (= :checked (:status (off-diagonal-example true 0 0))))
  (is (= :checked (:status (off-diagonal-example false 2 2))))
  ;; Reusing that proof to claim zero error for the identity kernel fails.
  (is (= :rejected (:status (off-diagonal-example false 2 0)))))
