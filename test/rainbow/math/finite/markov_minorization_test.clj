(ns rainbow.math.finite.markov-minorization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-minorization :as target]))

(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
    (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
    (target/extend-environment (:environment cp)))))

(deftest minorization-certificates-are-kernel-checked-and-axiom-free
  (let [env @checked-environment ids (merge (target/definition-ids env) (target/theorem-ids env))]
    (is (= #{'markov/nnrat-kernel-minorizes 'markov/nnrat-common-total-at-least-minorizing-mass
             'markov/signed-kernel-dobrushin-at-most-of-minorization
             'markov/signed-kernel-dobrushin-at-most-of-positive-minorization} (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (prn {:minorization-ids ids})))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [[:zero]]) xs))
(def nat (c 'data/Nat))
(def rat (c 'nnrat/NonnegativeRational))
(def zero (c 'nnrat/zero))
(def one (c 'nnrat/one))
(def half (c 'nnrat/half))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(def states (app 'finset-data/range (numeral 2)))
(defn- member [x] (poly 'list/membership nat (poly 'finset-data/enumeration nat states) x))
(defn- total [mass] (poly 'probability/nnrat-total-mass nat states mass))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- rational-equality [a b]
  (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat
    (app 'nat/multiply (app 'nnrat/numerator a) (app 'nnrat/denominator b))))
(defn- row [a b]
  (f/lam [['index nat]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
      (f/lam [['ignored nat]] rat) a (f/lam [['previous nat] ['acc rat]] b) 'index)))
(def row-a (row one zero))
(def row-b (row half half))
(def transition
  (f/lam [['source nat]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
      (f/lam [['ignored nat]] (f/arrow nat rat)) row-a
      (f/lam [['previous nat] ['acc (f/arrow nat rat)]] row-b) 'source)))

(def normalized
  (let [motive (f/lam [['source nat]] (eqv (total (f/app transition 'source)) one))]
    (f/lam [['source nat]]
      (f/app (f/const* 'data/Nat.rec [[:zero]]) motive (rational-equality (total row-a) one)
        (f/lam [['previous nat] ['ih (f/app motive 'previous)]] (rational-equality (total row-b) one))
        'source))))

(def half-at-most-one
  (app 'nnrat/at-most-from-cross half one
    (f/app (f/const* 'proposition/witness [[:succ [:zero]]]) nat
      (f/lam [['extra nat]]
        (f/equality [:succ [:zero]] nat (app 'algebra/nat-add (numeral 1) 'extra) (numeral 2)))
      (numeral 1) (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat (numeral 2)))))

(defn- pointwise-row-bound [mass values first-bound rest-bound]
  (let [motive (f/lam [['column nat]] (le (f/app mass 'column) (f/app values 'column)))]
    (f/lam [['column nat]]
      (f/app (f/const* 'data/Nat.rec [[:zero]]) motive first-bound
        (f/lam [['previous nat] ['ih (f/app motive 'previous)]] rest-bound) 'column))))

(defn- minorization-proof [mass first-a first-b]
  (let [a-bound (pointwise-row-bound mass row-a first-a (app 'nnrat/at-most-reflexive zero))
        b-bound (pointwise-row-bound mass row-b first-b (app 'nnrat/zero-at-most half))
        motive (f/lam [['source nat]]
                 (f/forall [['column nat]] (le (f/app mass 'column) (f/app transition 'source 'column))))
        global (f/lam [['source nat]]
                 (f/app (f/const* 'data/Nat.rec [[:zero]]) motive a-bound
                   (f/lam [['previous nat] ['ih (f/app motive 'previous)]] b-bound) 'source))]
    (f/lam [['source nat] ['source-member (member 'source)]
            ['column nat] ['column-member (member 'column)]]
      (f/app global 'source 'column))))

(defn- check [proof statement]
  (let [env @checked-environment
        core (fn [s] (let [r (elaborate/core-expression env s)]
                       (when-not (= :elaborated (:status r)) (throw (ex-info "Example elaboration failed" r)))
                       (:term r)))]
    (binding [kernel/*reduction-budget* 4000000]
      (kernel/check env (core proof) (core statement) #{}))))

(deftest sparse-nonidentical-rows-admit-a-strict-shared-mass-certificate
  ;; K = [[1,0],[1/2,1/2]] has a zero entry; nu = [1/2,0] is shared.
  ;; Its normalized row distance is 1/2, so rho=1/2 is sharp in this example.
  (doseq [[label mass first-a first-b rho positive? expected]
           [[:sparse-sharp (row half zero) half-at-most-one (app 'nnrat/at-most-reflexive half) half false :checked]
            [:insufficient-budget (row half zero) half-at-most-one (app 'nnrat/at-most-reflexive half) zero false :rejected]
            [:false-minorization (row one zero) (app 'nnrat/at-most-reflexive one)
             (app 'nnrat/at-most-reflexive one) zero false :rejected]
            [:zero-mass-nonstrict (row zero zero) (app 'nnrat/zero-at-most one)
             (app 'nnrat/zero-at-most half) one false :checked]
            [:positive-mass-construction (row half zero) half-at-most-one
             (app 'nnrat/at-most-reflexive half) nil true :checked]
            [:false-positive-total (row zero zero) (app 'nnrat/zero-at-most one)
             (app 'nnrat/zero-at-most half) nil true :rejected]]]
    (let [minorizes (minorization-proof mass first-a first-b)
          dp (app 'nnrat/denominator-predecessor (total mass))
          rho (if positive? (app 'nnrat/make dp dp) rho)
          budget (app 'nnrat/add rho (total mass))
          proof (if positive?
                  (poly 'markov/signed-kernel-dobrushin-at-most-of-positive-minorization
                        nat states transition mass normalized minorizes (c 'nnrat/one-positive))
                  (poly 'markov/signed-kernel-dobrushin-at-most-of-minorization
                        nat states transition mass normalized minorizes rho
                        (app 'nnrat/equivalent-to-at-most one budget (rational-equality one budget))))
          statement (app 'signed/at-most
                         (poly 'markov/signed-kernel-dobrushin-coefficient nat states transition)
                         (app 'signed/from-nnrat rho))]
      (is (= expected (:status (check proof statement))) (str label)))))
