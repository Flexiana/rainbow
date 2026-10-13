(ns rainbow.math.rational.signed.structural-equality-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.structural-equality :as structural]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(defn- app [f & args] (apply function/app f args))
(defn- nat [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (nat (dec n)))))
(defn- fraction [numerator denominator]
  (app (function/const* 'nnrat/make []) (nat numerator) (nat (dec denominator))))
(defn- signed-value [p-num p-den n-num n-den]
  (app (function/const* 'signed/make [])
       (fraction p-num p-den) (fraction n-num n-den)))
(defn- decide [a b]
  (app (function/const* 'signed/decide-structural-equal []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- reflexive-bool [v]
  (app (function/const* 'equality/reflexive [type-level]) bool v))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(def computation-specs
  "The quotient-versus-structure distinction, pinned at worked values: 1/2 and
  2/4 are EQUIVALENT (the quotient decision says true elsewhere) but decide
  STRUCTURALLY unequal here, which is exactly the property a translation
  certificate needs."
  [{:name 'signed-structural-test/same-pair :universes []
    :type (eq-bool (decide (signed-value 1 2 0 1) (signed-value 1 2 0 1))
                   true-value)
    :value (reflexive-bool true-value)}
   {:name 'signed-structural-test/equivalent-but-different :universes []
    :type (eq-bool (decide (signed-value 1 2 0 1) (signed-value 2 4 0 1))
                   false-value)
    :value (reflexive-bool false-value)}
   {:name 'signed-structural-test/negative-part-differs :universes []
    :type (eq-bool (decide (signed-value 1 2 0 1) (signed-value 1 2 1 1))
                   false-value)
    :value (reflexive-bool false-value)}])

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (structural/extend-environment (:environment checkpoint))
       :signed-structural-test computation-specs))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest structural-equality-decision-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (structural/definition-ids env) (structural/theorem-ids env))]
    (is (= 10 (count ids)))
    (doseq [[name id] ids]
      (is (some? id) (str name))
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest the-decision-separates-structure-from-the-quotient
  (let [env @checked-environment]
    (doseq [spec computation-specs]
      (let [id (environment/resolve-id env (:name spec))]
        (is (some? id) (str (:name spec)))
        (is (checked? env id) (str (:name spec)))))))
