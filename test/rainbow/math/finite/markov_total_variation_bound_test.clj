(ns rainbow.math.finite.markov-total-variation-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-total-variation-bound :as bound]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (bound/extend-environment (:environment checkpoint)))))

(deftest normalized-row-bound-is-kernel-checked-and-axiom-free
  (let [env @checked-environment
        ids (merge (bound/definition-ids env) (bound/theorem-ids env))]
    (is (= 6 (count ids)))
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
(defn- check-surface [value type]
  (let [env @checked-environment
        elaborate (fn [surface]
                    (let [result (elaborate/core-expression env surface)]
                      (when-not (= :elaborated (:status result))
                        (throw (ex-info "Example did not elaborate" result)))
                      (:term result)))]
    (:status (kernel/check env (elaborate value) (elaborate type) #{}))))

(defn- equivalent-example [left right]
  (check-surface
   (f/app (f/const* 'equality/reflexive [bound/type-level])
          (c 'data/Nat)
          (f/app (c 'nat/multiply)
                 (f/app (c 'nnrat/numerator) left)
                 (f/app (c 'nnrat/denominator) right)))
   (f/app (c 'nnrat/equivalent) left right)))

(defn- first-and-rest [first-value rest-value]
  (f/lam [['n (c 'data/Nat)]]
    (f/app (f/const* 'data/Nat.rec [bound/type-level])
           (f/lam [['ignored (c 'data/Nat)]] bound/nnrat)
           first-value
           (f/lam [['previous (c 'data/Nat)] ['acc bound/nnrat]] rest-value)
           'n)))

(defn- tv [size left right]
  (f/app (f/const* 'markov/nnrat-normalized-total-variation [[:zero]])
         (c 'data/Nat) (f/app (c 'finset-data/range) (numeral size)) left right))

(deftest normalized-distance-computes-at-boundaries
  (let [zero (rational 0 1) one (rational 1 1)
        left (first-and-rest one zero)
        right (first-and-rest zero one)
        triples (first-and-rest (rational 3 1) zero)
        zeros (first-and-rest zero zero)]
    (is (= :checked (equivalent-example (tv 2 left right) one)))
    (is (= :checked (equivalent-example (tv 2 left left) zero)))
    (is (= :checked (equivalent-example (tv 0 left right) zero)))
    ;; Non-unit masses are legal inputs, but their distance can exceed one.
    (is (= :checked (equivalent-example (tv 1 triples zeros) (rational 3 2))))
    (is (= :rejected (equivalent-example (tv 1 triples zeros) one)))))

(deftest scalar-distance-bound-instantiates-on-noncanonical-rationals
  (doseq [[a b] [[(rational 0 1) (rational 0 3)]
                 [(rational 1 2) (rational 2 4)]
                 [(rational 7 3) (rational 1 2)]]]
    (is (= :checked
           (check-surface
            (f/app (c 'nnrat/distance-at-most-sum) a b)
            (f/app (c 'nnrat/at-most)
                   (f/app (c 'nnrat/distance) a b)
                   (f/app (c 'nnrat/add) a b)))))))
