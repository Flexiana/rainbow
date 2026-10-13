(ns rainbow.math.finite.markov-dobrushin-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-dobrushin-statement :as statement]
            [rainbow.math.finite.markov-dobrushin-contraction :as target]))
(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
    (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
    (target/extend-environment (:environment cp)))))
(deftest actual-contraction-inhabitant-is-kernel-checked
  (let [env @checked-environment]
    (doseq [[name id] (target/theorem-ids env)]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))
    ;; Check the independently assembled applied predicate, not a weakened wrapper.
    (let [expected (f/forall statement/parameters
                     (f/app (f/const* 'markov/nnrat-dobrushin-contraction-estimate [target/U])
                            'S 'states 'kernel 'rho))
          r (elaborate/core-expression env expected)
          d (environment/declaration env (environment/resolve-id env 'markov/nnrat-dobrushin-contraction))]
      (is (= :elaborated (:status r)))
      (is (= (:term r) (:rainbow/type d)))
      (is (= :checked (:status (kernel/check env (:rainbow/value d) (:term r) #{'u})))))))

(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def nat (c 'data/Nat))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- rational [n d] (app 'nnrat/make (numeral n) (numeral (dec d))))
(defn- choose [type a b]
  (f/lam [['n nat]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
      (f/lam [['ignored nat]] type) a
      (f/lam [['previous nat] ['acc type]] b) 'n)))
(defn- rational-equality [a b]
  (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat
    (app 'nat/multiply (app 'nnrat/numerator a) (app 'nnrat/denominator b))))
(defn- core [env value]
  (let [r (elaborate/core-expression env value)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Instance elaboration failed" r)))
    (:term r)))

(defn- concrete-contraction [identity? left right rho expected]
  (let [env @checked-environment z (rational 0 1) o (rational 1 1)
        first-row (choose nnrat o z) second-row (if identity? (choose nnrat z o) first-row)
        transition (choose (f/arrow nat nnrat) first-row second-row)
        states (app 'finset-data/range (numeral 2))
        total (fn [mass] (poly 'probability/nnrat-total-mass nat states mass))
        motive (f/lam [['state nat]] (app 'nnrat/equivalent (total (f/app transition 'state)) o))
        normalized (f/lam [['state nat]]
                     (f/app (f/const* 'data/Nat.rec [[:zero]]) motive
                       (rational-equality (total first-row) o)
                       (f/lam [['previous nat] ['ih (f/app motive 'previous)]]
                         (rational-equality (total second-row) o)) 'state))
        delta (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
        bound (app 'signed/from-nnrat rho)
        a (app 'nnrat/add (app 'signed/positive delta) (app 'signed/negative bound))
        b (app 'nnrat/add (app 'signed/positive bound) (app 'signed/negative delta))
        coefficient-bound (app 'nnrat/equivalent-to-at-most a b (rational-equality a b))
        proof (poly 'markov/nnrat-dobrushin-contraction nat states transition rho
                    normalized coefficient-bound left right (rational-equality (total left) (total right)))
        l1 (fn [a b] (poly 'markov/nnrat-total-variation nat states a b))
        step (fn [mass] (poly 'markov/nnrat-kernel-step nat states transition mass))
        lhs (l1 (step left) (step right)) rhs (app 'nnrat/multiply rho (l1 left right))
        expected-lhs (rational (first expected) 1) expected-rhs (rational (second expected) 1)
        ;; Order is a relation on raw rational representatives, not a quotient.
        ;; Even 0/4 and 0/1 need explicit equivalence transport at this boundary.
        transported (app 'nnrat/at-most-respects-equivalence
                         expected-lhs lhs expected-rhs rhs
                         (rational-equality expected-lhs lhs) (rational-equality expected-rhs rhs) proof)
        goal (app 'nnrat/at-most expected-lhs expected-rhs)]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core env transported) (core env goal) #{}))))

(deftest full-inhabitant-covers-zero-positive-and-rejects-false-premises
  (let [z (rational 0 1) o (rational 1 1)
        left (choose nnrat o z) right (choose nnrat z o)
        equivalent-left (choose nnrat (rational 2 2) (rational 0 2))
        empty-mass (choose nnrat z z)]
    (doseq [[label identity? a b rho expected status]
            [[:positive false left right z [0 0] :checked]
             [:zero-residual false left left z [0 0] :checked]
             [:noncanonical-zero false left equivalent-left z [0 0] :checked]
             [:zero-inputs false empty-mass empty-mass z [0 0] :checked]
             [:identity true left right o [2 2] :checked]
             [:bad-coefficient true left right z [2 0] :rejected]
             [:unequal-masses false left empty-mass z [1 0] :rejected]
             [:false-conclusion true left right o [2 0] :rejected]]]
      (is (= status (:status (concrete-contraction identity? a b rho expected))) (str label)))))
