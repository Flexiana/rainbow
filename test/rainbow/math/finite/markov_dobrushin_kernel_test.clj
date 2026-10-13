(ns rainbow.math.finite.markov-dobrushin-kernel-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (coefficient/extend-environment (:environment checkpoint)))))

(deftest coefficient-and-bounds-are-checked-and-axiom-free
  (let [env @checked-environment
        ids (merge (coefficient/definition-ids env) (coefficient/theorem-ids env))]
    (is (= 5 (count ids)))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value declaration)
                                              (:rainbow/type declaration)
                                              (set (:rainbow/universes declaration)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(defn- c [name] (f/const* name []))
(defn- numeral [n]
  (nth (iterate #(f/app (c 'data/succ) %) (c 'data/zero)) n))
(defn- rational [n d]
  (f/app (c 'nnrat/make) (numeral n) (numeral (dec d))))
(defn- choose-row [target first-value rest-value]
  (f/lam [['n (c 'data/Nat)]]
    (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]])
           (f/lam [['ignored (c 'data/Nat)]] target)
           first-value
           (f/lam [['previous (c 'data/Nat)] ['acc target]] rest-value) 'n)))
(defn- row [a b] (choose-row coefficient/nnrat a b))
(defn- kernel-of [a b]
  (choose-row (f/arrow (c 'data/Nat) coefficient/nnrat) a b))
(defn- delta [size transition]
  (f/app (f/const* 'markov/signed-kernel-dobrushin-coefficient [[:zero]])
         (c 'data/Nat) (f/app (c 'finset-data/range) (numeral size)) transition))

(defn- equivalent-example [left expected]
  (let [env @checked-environment
        right (f/app (c 'signed/from-nnrat) expected)
        a (f/app (c 'nnrat/add) (f/app (c 'signed/positive) left)
                 (f/app (c 'signed/negative) right))
        b (f/app (c 'nnrat/add) (f/app (c 'signed/positive) right)
                 (f/app (c 'signed/negative) left))
        proof (f/app (f/const* 'equality/reflexive [[:succ [:zero]]])
                     (c 'data/Nat)
                     (f/app (c 'nat/multiply)
                            (f/app (c 'nnrat/numerator) a)
                            (f/app (c 'nnrat/denominator) b)))
        type (f/app (c 'signed/equivalent) left right)
        core (fn [surface]
               (let [r (elaborate/core-expression env surface)]
                 (when-not (= :elaborated (:status r))
                   (throw (ex-info "Coefficient example failed elaboration" r)))
                 (:term r)))]
    (kernel/check env (core proof) (core type) #{})))

(deftest coefficient-computes-over-all-row-pairs
  (let [zero (rational 0 1) one (rational 1 1) half (rational 1 2)
        first-row (row one zero)
        identity-kernel (kernel-of first-row (row zero one))
        identical-rows (kernel-of first-row first-row)
        partial-mixing (kernel-of first-row (row half half))
        nonnormalized (kernel-of (row (rational 3 1) zero)
                                 (row zero (rational 3 1)))]
    (doseq [[label value expected]
            [[:disjoint (delta 2 identity-kernel) one]
             [:identical (delta 2 identical-rows) zero]
             [:half (delta 2 partial-mixing) half]
             [:empty (delta 0 identity-kernel) zero]
             [:singleton (delta 1 identity-kernel) zero]
             [:non-unit-masses (delta 2 nonnormalized) (rational 3 1)]]]
      ;; The half-valued example exhausts the default 1M reduction budget.
      ;; Keep the larger, still bounded allowance local to that computation.
      (let [result (binding [kernel/*reduction-budget*
                             (if (= label :half) 4000000 kernel/*reduction-budget*)]
                     (equivalent-example value expected))]
        (is (= :checked (:status result)) (str label " " result))))
    ;; A diagonal-only or first-row-only maximum would incorrectly give zero.
    (is (= :rejected (:status (equivalent-example (delta 2 identity-kernel) zero))))))

(deftest coefficient-replay-preserves-content-identities
  (let [env @checked-environment
        replayed (support/extend-with env :finite-markov-dobrushin-kernel
                   (concat coefficient/definition-specs coefficient/theorem-specs))]
    (is (= (coefficient/definition-ids env) (coefficient/definition-ids replayed)))
    (is (= (coefficient/theorem-ids env) (coefficient/theorem-ids replayed)))))
