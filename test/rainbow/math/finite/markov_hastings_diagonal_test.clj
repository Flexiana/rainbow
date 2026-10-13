(ns rainbow.math.finite.markov-hastings-diagonal-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-hastings-diagonal :as diagonal]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat-type (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- app [f & args] (apply function/app f args))
(defn- numeral [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (numeral (dec n)))))
(defn- whole [n]
  (app (function/const* 'nnrat/make []) (numeral n) (numeral 0)))
(defn- req [l r] (app (function/const* 'nnrat/equivalent []) l r))
(defn- reflexive-req [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))

(def mass
  "index 0 gets 1/1, everything else 2/1 -- enough to tell slots apart."
  (function/lam
   [['state nat-type]]
   (app (function/const* 'data/Nat.rec [type-level])
        (function/lam [['ignored nat-type]] nnrat)
        (whole 1)
        (function/lam [['predecessor nat-type] ['recursive nnrat]] (whole 2))
        'state)))

(defn- placed [x y]
  (app (function/const* 'mcmc/diagonal-placement [zero-level])
       nat-type (function/const* 'nat/decide-equality []) mass
       (numeral x) (numeral y)))

(def computation-specs
  "The canonical placement over Nat with nat/decide-equality, at literals:
  diagonal slots carry their mass, off-diagonal slots are zero, by reflexivity."
  [{:name 'hastings-diagonal-test/diagonal-zero :universes []
    :type (req (placed 0 0) (whole 1)) :value (reflexive-req (whole 1))}
   {:name 'hastings-diagonal-test/diagonal-one :universes []
    :type (req (placed 1 1) (whole 2)) :value (reflexive-req (whole 2))}
   {:name 'hastings-diagonal-test/off-diagonal :universes []
    :type (req (placed 0 1) (whole 0)) :value (reflexive-req (whole 0))}
   {:name 'hastings-diagonal-test/off-diagonal-reverse :universes []
    :type (req (placed 1 0) (whole 0)) :value (reflexive-req (whole 0))}])

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (diagonal/extend-environment (:environment checkpoint))
       :hastings-diagonal-test computation-specs))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest diagonal-placement-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (diagonal/definition-ids env) (diagonal/theorem-ids env))]
    (is (= 5 (count ids)))
    (doseq [[name id] ids]
      (is (some? id) (str name))
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest nat-decide-equality-is-such-a-decider-at-worked-values
  (testing "for indexed state spaces the existing nat decider suffices; the
            placement computes mass on the diagonal and zero off it"
    (let [env @checked-environment]
      (doseq [spec computation-specs]
        (let [id (environment/resolve-id env (:name spec))]
          (is (some? id) (str (:name spec)))
          (is (checked? env id) (str (:name spec))))))))
