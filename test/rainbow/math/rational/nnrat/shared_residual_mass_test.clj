(ns rainbow.math.rational.nnrat.shared-residual-mass-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.shared-residual-mass :as residual]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (residual/extend-environment (:environment checkpoint)))))

(deftest decomposition-is-kernel-checked-and-axiom-free
  (let [env @checked-environment
        ids (merge (residual/definition-ids env) (residual/theorem-ids env))]
    (is (= 7 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d)
                                              (:rainbow/type d) #{}))) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))

(defn- c [name] (f/const* name []))
(defn- numeral [n]
  (nth (iterate #(f/app (c 'data/succ) %) (c 'data/zero)) n))
(defn- rational [[n d]]
  (f/app (c 'nnrat/make) (numeral n) (numeral (dec d))))
(defn- example [name a b expected]
  (let [env @checked-environment
        value (f/app (c name) (rational a) (rational b))
        target (rational expected)
        cross (f/app (c 'nat/multiply) (f/app (c 'nnrat/numerator) value)
                     (f/app (c 'nnrat/denominator) target))
        proof (f/app (f/const* 'equality/reflexive [[:succ [:zero]]])
                     (c 'data/Nat) cross)
        type (f/app (c 'nnrat/equivalent) value target)
        core (fn [term]
               (let [r (elaborate/core-expression env term)]
                 (when-not (= :elaborated (:status r))
                   (throw (ex-info "Example failed elaboration" r)))
                 (:term r)))]
    (kernel/check env (core proof) (core type) #{})))

(deftest residuals-compute-for-both-orders-ties-and-zero
  (doseq [[a b p q] [[[1 1] [0 1] [1 1] [0 1]]
                     [[0 1] [1 1] [0 1] [1 1]]
                     [[1 2] [2 4] [0 1] [0 1]]
                     [[2 1] [1 2] [3 2] [0 1]]
                     [[0 3] [0 1] [0 1] [0 1]]]]
    (is (= :checked (:status (example 'nnrat/left-residual-mass a b p))))
    (is (= :checked (:status (example 'nnrat/right-residual-mass a b q))))))

(deftest wrong-residual-is-rejected
  (let [r (example 'nnrat/left-residual-mass [1 1] [0 1] [0 1])]
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (get-in r [:error :error/category])))))
