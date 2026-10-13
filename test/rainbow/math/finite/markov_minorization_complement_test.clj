(ns rainbow.math.finite.markov-minorization-complement-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-minorization-complement :as target]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
           (target/extend-environment (:environment cp)))))

(deftest exact-complement-declarations-are-checked-and-axiom-free
  (let [env @checked-environment ids (target/theorem-ids env)]
    (is (= #{'markov/nnrat-minorizing-total-at-most-one
             'nnrat/one-at-most-distance-complement-plus-mass
             'markov/signed-kernel-dobrushin-at-most-of-exact-minorization} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d))))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:exact-minorization-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [[:zero]]) xs))
(def nat (c 'data/Nat))
(def zero (c 'nnrat/zero))
(def one (c 'nnrat/one))
(def half (c 'nnrat/half))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(def states (app 'finset-data/range (numeral 2)))
(defn- member [x] (poly 'list/membership nat (poly 'finset-data/enumeration nat states) x))
(defn- total [mass] (poly 'probability/nnrat-total-mass nat states mass))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- rational-equality [a b]
  (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat
    (app 'nat/multiply (app 'nnrat/numerator a) (app 'nnrat/denominator b))))
(defn- check [proof statement]
  (let [env @checked-environment
        core (fn [s] (let [r (elaborate/core-expression env s)]
                       (when-not (= :elaborated (:status r)) (throw (ex-info "Example elaboration failed" r)))
                       (:term r)))]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core proof) (core statement) #{}))))

(def anchor-member
  (let [anchor (numeral 1) rest-member (poly 'list/membership nat
                   (f/app (f/const* 'data/cons [[:succ [:zero]]]) nat (numeral 0)
                     (f/app (f/const* 'data/nil [[:succ [:zero]]]) nat)) anchor)
        self-equal (f/equality [:succ [:zero]] nat anchor anchor)]
    (app 'proposition/left-disjunct self-equal rest-member
      (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat anchor))))

(deftest exact-factor-uses-rational-mass-not-its-raw-denominator
  (let [row (f/lam [['column nat]] half)
        transition (f/lam [['source nat]] row)
        normalized (f/lam [['source nat]] (rational-equality (total row) one))]
    (doseq [[label entry expected-rho valid?]
            [[:half half zero true]
             [:unreduced-half (app 'nnrat/make (numeral 2) (numeral 3)) zero true]
             [:zero-mass zero one true]
             [:false-domination one one false]]]
      (let [mass (f/lam [['column nat]] entry)
            amount (total mass) rho (app 'nnrat/distance amount one)
            entry-bound (if (= label :zero-mass)
                          (app 'nnrat/zero-at-most half)
                          (app 'nnrat/equivalent-to-at-most entry half (rational-equality entry half)))
            minorizes (f/lam [['source nat] ['source-member (member 'source)]
                              ['column nat] ['column-member (member 'column)]] entry-bound)
            arguments [nat states transition mass normalized minorizes (numeral 1) anchor-member]
            total-proof (apply poly 'markov/nnrat-minorizing-total-at-most-one arguments)
            bound-proof (apply poly 'markov/signed-kernel-dobrushin-at-most-of-exact-minorization arguments)
            bound (app 'signed/at-most
                    (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
                    (app 'signed/from-nnrat rho))
            status (if valid? :checked :rejected)]
        (is (= :checked (:status (check (rational-equality rho expected-rho) (eqv rho expected-rho)))) (str label))
        (is (= status (:status (check total-proof (app 'nnrat/at-most amount one)))) (str label))
        (is (= status (:status (check bound-proof bound))) (str label))))))

(deftest normalization-is-load-bearing-for-the-complement-bound
  ;; The unscaled identity has delta=1 and accepts rho=1 with zero minorizer.
  ;; Scaling both diagonal entries to 2 gives row mass 2 and host delta=2:
  ;; the same proposed rho=1 is false, and its normalization witness must fail.
  (let [rat (c 'nnrat/NonnegativeRational)
        row (fn [left right]
              (f/lam [['column nat]]
                (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
                  (f/lam [['ignored nat]] rat) left
                  (f/lam [['previous nat] ['acc rat]] right) 'column)))
        mass (f/lam [['column nat]] zero)]
    (doseq [[entry expected] [[one :checked]
                              [(app 'nnrat/make (numeral 2) (numeral 0)) :rejected]]]
      (let [first-row (row entry zero) second-row (row zero entry)
            transition
            (f/lam [['source nat]]
              (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
                (f/lam [['ignored nat]] (f/arrow nat rat)) first-row
                (f/lam [['previous nat] ['acc (f/arrow nat rat)]] second-row) 'source))
            motive (f/lam [['source nat]] (eqv (total (f/app transition 'source)) one))
            normalized
            (f/lam [['source nat]]
              (f/app (f/const* 'data/Nat.rec [[:zero]]) motive
                (rational-equality (total first-row) one)
                (f/lam [['previous nat] ['ih (f/app motive 'previous)]]
                  (rational-equality (total second-row) one)) 'source))
            minorizes
            (f/lam [['source nat] ['source-member (member 'source)]
                    ['column nat] ['column-member (member 'column)]]
              (app 'nnrat/zero-at-most (f/app transition 'source 'column)))
            rho (app 'nnrat/distance (total mass) one)
            proof (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-minorization
                    nat states transition mass normalized minorizes (numeral 1) anchor-member)
            statement (app 'signed/at-most
                        (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
                        (app 'signed/from-nnrat rho))]
        (is (= expected (:status (check proof statement))) (str expected))))))
