(ns rainbow.math.finite.markov-column-exact-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.complement-proper :as scalar]
            [rainbow.math.finite.markov-column-exact-contraction :as target]
            [rainbow.math.finite.markov-minorization-test :as sparse]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
           (target/extend-environment (:environment cp)))))

(deftest proper-factor-declarations-are-checked-and-axiom-free
  (let [env @checked-environment ids (merge (scalar/theorem-ids env) (target/theorem-ids env))]
    (is (= #{'nat/distance-at-most-upper-of-at-most
             'nnrat/distance-to-one-proper-of-positive-at-most-one
             'markov/nnrat-exact-minorization-factor-proper
             'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum
             'markov/nnrat-exact-column-minimum-factor-proper
             'markov/nnrat-exact-column-minimum-contraction
             'markov/nnrat-exact-column-minimum-geometric-decay
             'markov/nnrat-exact-column-minimum-stationary-pointwise-unique
             'markov/nnrat-exact-column-minimum-geometric-convergence-to-stationary} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d))))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:proper-factor-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [[:zero]]) xs))
(def nat (c 'data/Nat))
(def one (c 'nnrat/one))
(def level [:succ [:zero]])
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- eqn [a b] (f/equality level nat a b))
(defn- refl [a] (f/app (f/const* 'equality/reflexive [level]) nat a))
(defn- witness [predicate extra proof]
  (f/app (f/const* 'proposition/witness [level]) nat predicate extra proof))
(defn- check [proof statement]
  (let [env @checked-environment
        core (fn [s] (let [r (elaborate/core-expression env s)]
                       (when-not (= :elaborated (:status r)) (throw (ex-info "Example elaboration failed" r)))
                       (:term r)))]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core proof) (core statement) #{}))))

(deftest scalar-properness-requires-both-positivity-and-the-unit-bound
  (doseq [[n d expected] [[1 2 :checked] [2 4 :checked] [1 1 :checked]
                         [0 2 :rejected] [3 2 :rejected]]]
    (let [value (app 'nnrat/make (numeral n) (numeral (dec d)))
          left (app 'nat/multiply (app 'nnrat/numerator value) (app 'nnrat/denominator one))
          right (app 'nat/multiply (app 'nnrat/numerator one) (app 'nnrat/denominator value))
          bounded (app 'nnrat/at-most-from-cross value one
                    (witness (f/lam [['extra nat]] (eqn (app 'algebra/nat-add left 'extra) right))
                             (numeral (max 0 (- d n))) (refl right)))
          positive (witness (f/lam [['extra nat]]
                              (eqn (app 'algebra/nat-add (numeral 1) 'extra) (numeral n)))
                            (numeral (max 0 (dec n))) (refl (numeral n)))
          rho (app 'nnrat/distance value one)
          proof (app 'nnrat/distance-to-one-proper-of-positive-at-most-one value bounded positive)]
      (is (= expected (:status (check proof (scalar/proper rho)))) (str [n d])))))

(defn- anchor-member [n]
  (let [x (numeral n)
        tail (f/app (f/const* 'data/cons [level]) nat (numeral 0)
                    (f/app (f/const* 'data/nil [level]) nat))]
    (app 'proposition/left-disjunct (eqn x (numeral 1))
         (poly 'list/membership nat tail x) (refl x))))

(deftest sparse-column-minimum-supplies-an-exact-proper-coefficient
  (doseq [[anchor expected] [[1 :checked] [2 :rejected]]]
    (let [mass (poly 'markov/nnrat-column-minimum-mass nat sparse/states sparse/transition (numeral anchor))
          amount (poly 'probability/nnrat-total-mass nat sparse/states mass)
          rho (app 'nnrat/distance amount one)
          arguments [nat sparse/states sparse/transition (numeral anchor) (anchor-member anchor) sparse/normalized]
          bound-proof (apply poly 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum arguments)
          proper-proof (apply poly 'markov/nnrat-exact-column-minimum-factor-proper
                              (conj arguments (c 'nnrat/one-positive)))
          bound (app 'signed/at-most
                  (poly 'markov/signed-kernel-dobrushin-coefficient nat sparse/states sparse/transition)
                  (app 'signed/from-nnrat rho))]
      (is (= expected (:status (check bound-proof bound))) (str anchor))
      (is (= expected (:status (check proper-proof (scalar/proper rho)))) (str anchor)))))

(deftest exact-column-contraction-produces-the-distance-inequality
  (let [zero-mass (f/lam [['index nat]] (c 'nnrat/zero))
        total (fn [mass] (poly 'probability/nnrat-total-mass nat sparse/states mass))
        l1 (fn [a b] (poly 'markov/nnrat-total-variation nat sparse/states a b))
        step (fn [mass] (poly 'markov/nnrat-kernel-step nat sparse/states sparse/transition mass))]
    (doseq [[label anchor left right expected]
            [[:different-probabilities 1 sparse/row-a sparse/row-b :checked]
             [:zero-totals 1 zero-mass zero-mass :checked]
             [:false-equal-total 1 sparse/row-a zero-mass :rejected]
             [:outside-anchor 2 sparse/row-a sparse/row-b :rejected]]]
      (let [mass (poly 'markov/nnrat-column-minimum-mass nat sparse/states sparse/transition (numeral anchor))
            rho (app 'nnrat/distance (total mass) one)
            equal-total (refl (app 'nat/multiply (app 'nnrat/numerator (total left))
                                  (app 'nnrat/denominator (total right))))
            proof (poly 'markov/nnrat-exact-column-minimum-contraction
                        nat sparse/states sparse/transition (numeral anchor) (anchor-member anchor)
                        sparse/normalized left right equal-total)
            statement (app 'nnrat/at-most (l1 (step left) (step right))
                           (app 'nnrat/multiply rho (l1 left right)))]
        (is (= expected (:status (check proof statement))) (str label))
        (when (= label :different-probabilities)
          ;; A fully applied inequality proof does not inhabit the forall predicate.
          (is (= :rejected (:status
                            (check proof (poly 'markov/nnrat-dobrushin-contraction-estimate
                                               nat sparse/states sparse/transition rho))))))))))
