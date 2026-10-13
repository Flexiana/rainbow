(ns rainbow.math.nat.ring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]))

(def nat (function/const* 'data/Nat []))
(def type-level [:succ [:zero]])
(defn- eq-nat [l r] (function/equality type-level nat l r))
(defn- m [l r] (ring/nmul l r))
(defn- p [l r] (ring/nadd l r))

;; product-equality cases over free nat variables a b c d e
(def cases
  [{:name 'ringtest/assoc  :vars '[a b c]
    :lhs (m (m 'a 'b) 'c) :rhs (m 'a (m 'b 'c))}
   {:name 'ringtest/comm   :vars '[a b]
    :lhs (m 'a 'b) :rhs (m 'b 'a)}
   {:name 'ringtest/four-reorder :vars '[a b c d]
    :lhs (m (m 'a 'b) (m 'c 'd)) :rhs (m (m 'a 'c) (m 'b 'd))}
   {:name 'ringtest/full-reverse :vars '[a b c d]
    :lhs (m (m 'a 'b) (m 'c 'd)) :rhs (m (m 'd 'c) (m 'b 'a))}
   {:name 'ringtest/repeats :vars '[a b]
    :lhs (m (m 'a 'a) 'b) :rhs (m (m 'b 'a) 'a)}
   {:name 'ringtest/single :vars '[a]
    :lhs 'a :rhs 'a}
   {:name 'ringtest/deep :vars '[a b c d]
    :lhs (m (m (m 'a 'b) 'c) 'd) :rhs (m 'a (m 'b (m 'c 'd)))}
   {:name 'ringtest/degree5 :vars '[a b c d e]
    :lhs (m (m 'a (m 'b 'c)) (m 'd 'e))
    :rhs (m (m 'e 'd) (m 'c (m 'b 'a)))}])

;; sum / distribution cases proved via the full normalizer prove-nat-eq
(def sum-cases
  [{:name 'ringtest/add-comm :vars '[a b]
    :lhs (p 'a 'b) :rhs (p 'b 'a)}
   {:name 'ringtest/add-assoc :vars '[a b c]
    :lhs (p (p 'a 'b) 'c) :rhs (p 'a (p 'b 'c))}
   {:name 'ringtest/distribute-left :vars '[a b c]
    :lhs (m 'a (p 'b 'c)) :rhs (p (m 'a 'b) (m 'a 'c))}
   {:name 'ringtest/distribute-right :vars '[a b m]
    :lhs (m (p 'a 'b) 'm) :rhs (p (m 'a 'm) (m 'b 'm))}
   {:name 'ringtest/foil :vars '[a b c d]
    :lhs (m (p 'a 'b) (p 'c 'd))
    :rhs (p (p (m 'a 'c) (m 'b 'c)) (p (m 'a 'd) (m 'b 'd)))}
   ;; the exact nnrat right-distributivity nat obligation: numL*denR = numR*denL,
   ;; degree-7 monomials, heavily reordered (this is what unlocks nnrat distributivity)
   {:name 'ringtest/nnrat-distrib :vars '[na nb da db nm dm]
    :lhs (m (m (p (m 'na 'db) (m 'nb 'da)) 'nm) (m (m 'da 'dm) (m 'db 'dm)))
    :rhs (m (p (m (m 'na 'nm) (m 'db 'dm)) (m (m 'nb 'nm) (m 'da 'dm)))
            (m (m 'da 'db) 'dm))}])

(defn- case->spec [{:keys [name vars lhs rhs]}]
  (let [bindings (mapv (fn [v] [v nat]) vars)]
    {:name name :universes []
     :type (function/forall bindings (eq-nat lhs rhs))
     :value (function/lam bindings (:proof (ring/prove-product-eq lhs rhs)))}))

(defn- sum-case->spec [{:keys [name vars lhs rhs]}]
  (let [bindings (mapv (fn [v] [v nat]) vars)]
    {:name name :universes []
     :type (function/forall bindings (eq-nat lhs rhs))
     :value (function/lam bindings (:proof (ring/prove-nat-eq lhs rhs)))}))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (support/extend-with (:environment c) :nat-ring-test
                           (into (mapv case->spec cases)
                                 (mapv sum-case->spec sum-cases))))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest nat-ring-normalizer-emits-axiom-free-proofs
  (let [env @checked-environment
        ids (support/spec-ids env (into (mapv case->spec cases)
                                        (mapv sum-case->spec sum-cases)))]
    (is (= (into (set (map :name cases)) (map :name sum-cases))
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))

;; negative checks: non-identities must be rejected by the tactic (no false proof)
(deftest nat-ring-rejects-non-identities
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-product-eq (m 'a 'b) (m 'a 'c))))
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-nat-eq (p 'a 'a) 'a)))
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-nat-eq (m 'a (p 'b 'c)) (p (m 'a 'b) 'c)))))
