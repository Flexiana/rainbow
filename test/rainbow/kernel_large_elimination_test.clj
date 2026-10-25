(ns rainbow.kernel-large-elimination-test
  "A recursor of an inductive type with two or more constructors may not eliminate a proposition into a
  larger universe: with the opt-in proof-irrelevance axiom that derived False (inl = inr in
  Sum.{0,0} truth truth, told apart by Sum.rec into Bool). Universe-polymorphic uses record the
  requirement on the declaration and every instantiation must keep it."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.profile :as profile]))

(def base
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "Checkpoint rejected" {})))
           (:environment cp))))
(def Z [:zero])
(def O [:succ [:zero]])
(defn- core [env e] (:term (elaborate/core-expression env e)))
(defn- rec-type [env alias levels]
  (kernel/infer env [:const (environment/resolve-id env alias) levels] #{}))
(defn- large-elim-rejected? [r]
  (and (= :rejected (:status r)) (= :kernel/large-elimination-from-prop (get-in r [:error :error/category]))))

(deftest propositions-with-several-constructors-eliminate-only-into-prop
  (let [env @base]
    (is (large-elim-rejected? (rec-type env 'data/Sum.rec [Z Z O])))
    (is (large-elim-rejected? (rec-type env 'data/Option.rec [Z O])))
    (is (large-elim-rejected? (rec-type env 'data/List.rec [Z O])))
    (is (= :checked (:status (rec-type env 'data/Sum.rec [Z Z Z]))) "into Prop is fine")
    (is (= :checked (:status (rec-type env 'data/Sum.rec [O O O]))) "a type is fine")
    (is (= :checked (:status (rec-type env 'data/Sum.rec [O Z O]))) "max 1 0 is a type")
    (is (= :checked (:status (rec-type env 'data/Product.rec [Z Z O]))) "one constructor is fine")
    (is (= :checked (:status (rec-type env 'data/Bool.rec [O]))))))

(deftest the-proof-of-false-from-proof-irrelevance-is-rejected
  (let [envp (:environment (profile/activate @base :proof-irrelevant))
        T (f/const* 'proposition/truth []) triv (f/const* 'proposition/trivial [])
        bool (f/const* 'data/Bool []) tt (f/const* 'data/true []) ff (f/const* 'data/false [])
        P (f/app (f/const* 'data/Sum [Z Z]) T T)
        a (f/app (f/const* 'data/left [Z Z]) T T triv)
        b (f/app (f/const* 'data/right [Z Z]) T T triv)
        pi (f/app (f/const* 'logic/proof-irrelevance []) P a b)
        fsel (f/lam [['s P]] (f/app (f/const* 'data/Sum.rec [Z Z O]) T T (f/lam [['s0 P]] bool)
                                    (f/lam [['x T]] tt) (f/lam [['y T]] ff) 's))
        h (f/app (f/const* 'equality/congruent-function [Z O]) P bool fsel a b pi)
        D (f/lam [['c bool]] (f/app (f/const* 'data/Bool.rec [O]) (f/lam [['c0 bool]] 'Prop)
                                    (f/const* 'proposition/falsity []) T 'c))
        proof (f/app (f/const* 'equality/substitution [O]) bool tt ff h D triv)
        r (kernel/check envp (core envp proof) (core envp (f/const* 'proposition/falsity [])) #{})]
    (is (= :rejected (:status r)))
    (is (= :kernel/large-elimination-from-prop (get-in r [:error :error/category])))))

(deftest polymorphic-uses-carry-the-requirement
  (let [env @base
        length (environment/declaration env (environment/resolve-id env 'list/length))
        length-id (:rainbow/id length)]
    (is (= #{[:param (first (:rainbow/universes length))]} (:rainbow/level-requirements length)))
    (is (large-elim-rejected? (kernel/infer env [:const length-id [Z]] #{})))
    (is (= :checked (:status (kernel/infer env [:const length-id [O]] #{}))))
    ;; a definition over list/length at a parameter inherits the requirement; at 0 it is refused
    (let [u 'w
          ty (:type (kernel/infer env [:const length-id [[:param u]]] #{u}))
          d (kernel/add-declaration env {:rainbow/kind :definition :rainbow/aliases #{'probe/length-again}
                                         :rainbow/universes [u] :rainbow/type ty
                                         :rainbow/value [:const length-id [[:param u]]]
                                         :rainbow/transparency :reducible
                                         :rainbow/dependencies (into (rainbow.term/constants ty) #{length-id})})]
      (is (= :accepted (:status d)) (pr-str (:error d)))
      (is (= #{[:param u]} (:rainbow/level-requirements (:declaration d))))
      (let [env2 (:environment d) id (:rainbow/id (:declaration d))]
        (is (large-elim-rejected? (kernel/infer env2 [:const id [Z]] #{})))
        (is (= :checked (:status (kernel/infer env2 [:const id [O]] #{}))))))))
