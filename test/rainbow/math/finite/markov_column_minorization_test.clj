(ns rainbow.math.finite.markov-column-minorization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-column-minorization :as target]
            [rainbow.math.finite.markov-minorization-test :as sparse]))

(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
    (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
    (target/extend-environment (:environment cp)))))
(deftest column-minimum-construction-is-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (merge (target/definition-ids env) (target/theorem-ids env))]
    (is (= #{'markov/nnrat-column-minimum-mass 'markov/nnrat-column-minimum-mass-minorizes
             'markov/nnrat-column-minimum-mass-greatest
             'markov/signed-kernel-dobrushin-at-most-of-column-minimum-budget
             'markov/signed-kernel-dobrushin-at-most-of-positive-column-minimum} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:column-minorization-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [[:zero]]) xs))
(def nat sparse/nat)
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- mass [transition anchor]
  (poly 'markov/nnrat-column-minimum-mass nat sparse/states transition anchor))
(defn- total [mapping] (poly 'probability/nnrat-total-mass nat sparse/states mapping))
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

(deftest computes-the-sparse-minorizer-and-its-coefficient
  (let [computed (mass sparse/transition (numeral 0))
        amount (total computed)]
    (doseq [[actual expected] [[(f/app computed (numeral 0)) sparse/half]
                              [(f/app computed (numeral 1)) sparse/zero]
                              [amount sparse/half]]]
      (is (= :checked (:status (check (rational-equality actual expected) (eqv actual expected))))))
    (doseq [[rho expected] [[sparse/half :checked] [sparse/zero :rejected]]]
      (let [budget (app 'nnrat/add rho amount)
            proof (poly 'markov/signed-kernel-dobrushin-at-most-of-column-minimum-budget
                    nat sparse/states sparse/transition (numeral 0) sparse/normalized rho
                    (app 'nnrat/equivalent-to-at-most sparse/one budget (rational-equality sparse/one budget)))
            statement (app 'signed/at-most
                           (poly 'markov/signed-kernel-dobrushin-coefficient nat sparse/states sparse/transition)
                           (app 'signed/from-nnrat rho))]
        (is (= expected (:status (check proof statement))))))
    (let [dp (app 'nnrat/denominator-predecessor amount)
          rho (app 'nnrat/make dp dp)
          proof (poly 'markov/signed-kernel-dobrushin-at-most-of-positive-column-minimum
                  nat sparse/states sparse/transition (numeral 0) sparse/normalized (c 'nnrat/one-positive))]
      (is (= :checked (:status (check proof
                               (app 'signed/at-most
                                    (poly 'markov/signed-kernel-dobrushin-coefficient nat sparse/states sparse/transition)
                                    (app 'signed/from-nnrat rho)))))))))

(defn- list-of-nats [values]
  (reduce (fn [tail n] (f/app (f/const* 'data/cons [[:succ [:zero]]]) nat (numeral n) tail))
          (f/app (f/const* 'data/nil [[:succ [:zero]]]) nat) (reverse values)))
(defn- zero-or-false-membership [n]
  (let [x (numeral n) empty (list-of-nats [])
        x-one (f/equality [:succ [:zero]] nat x (numeral 1))
        x-zero (f/equality [:succ [:zero]] nat x (numeral 0))]
    (app 'proposition/right-disjunct x-one (poly 'list/membership nat (list-of-nats [0]) x)
      (app 'proposition/left-disjunct x-zero (poly 'list/membership nat empty x)
        (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat x)))))

(deftest listed-anchor-is-essential-to-greatest-minorizer-claim
  ;; Listed rows are all one; an outside anchor has a zero row. Including
  ;; that anchor still gives a valid lower mass, but not the greatest one.
  (let [row-value
        (f/lam [['source nat]]
          (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
            (f/lam [['ignored nat]] sparse/rat) sparse/one
            (f/lam [['previous nat] ['acc sparse/rat]]
              (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
                (f/lam [['ignored nat]] sparse/rat) sparse/one
                (f/lam [['prior nat] ['old sparse/rat]] sparse/zero) 'previous)) 'source))
        transition (f/lam [['source nat] ['column nat]] (f/app row-value 'source))
        good (mass transition (numeral 0))
        good-minorizes (poly 'markov/nnrat-column-minimum-mass-minorizes nat sparse/states transition (numeral 0))]
    (doseq [[anchor expected-value expected-status] [[0 sparse/one :checked] [2 sparse/zero :rejected]]]
      (let [computed (mass transition (numeral anchor))
            value (f/app computed (numeral 0))
            proof (poly 'markov/nnrat-column-minimum-mass-greatest nat sparse/states transition (numeral anchor)
                    (zero-or-false-membership anchor) good good-minorizes (numeral 0) (zero-or-false-membership 0))]
        (is (= :checked (:status (check (rational-equality value expected-value) (eqv value expected-value)))))
        (is (= expected-status (:status (check proof (app 'nnrat/at-most (f/app good (numeral 0)) value)))))))))
