(ns rainbow.math.finite.markov-full-support-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-full-support :as full-support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(defn- app [f & args] (apply function/app f args))
(defn- nat [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (nat (dec n)))))
(defn- fraction [numerator denominator]
  (app (function/const* 'nnrat/make []) (nat numerator) (nat (dec denominator))))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- reflexive-bool [v]
  (app (function/const* 'equality/reflexive [type-level]) bool v))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- index-of [n] (app (function/const* 'finite/Index []) (nat n)))
(defn- index-finset [n] (app (function/const* 'finite/index-finset []) (nat n)))
(defn- full-support [n target proposal]
  (app (function/const* 'mcmc/full-support-decision [[:zero]])
       (index-of n) (index-finset n) target proposal))

(def uniform-target
  "1/2 at every state of Index 2."
  (function/lam [['state (index-of 2)]] (fraction 1 2)))
(def uniform-proposal
  (function/lam [['source (index-of 2)] ['destination (index-of 2)]]
                (fraction 1 2)))
(def dead-target
  "Zero mass everywhere -- full support must decide FALSE."
  (function/lam [['state (index-of 2)]] (fraction 0 1)))

(def computation-specs
  [{:name 'full-support-test/uniform-decides-true :universes []
    :type (eq-bool (full-support 2 uniform-target uniform-proposal) true-value)
    :value (reflexive-bool true-value)}
   {:name 'full-support-test/dead-target-decides-false :universes []
    :type (eq-bool (full-support 2 dead-target uniform-proposal) false-value)
    :value (reflexive-bool false-value)}])

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (full-support/extend-environment (:environment checkpoint))
       :full-support-test computation-specs))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest the-full-support-api-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (full-support/definition-ids env)
                   (full-support/theorem-ids env))]
    (is (= 9 (count ids)))
    (doseq [[name id] ids]
      (is (some? id) (str name))
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest the-decision-computes-on-index-two
  (testing "a uniform model decides true and a dead target decides false --
            the boolean is executable, not just certified"
    (let [env @checked-environment]
      (doseq [spec computation-specs]
        (let [id (environment/resolve-id env (:name spec))]
          (is (some? id) (str (:name spec)))
          (is (checked? env id) (str (:name spec))))))))
