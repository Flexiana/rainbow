(ns rainbow.math.rational.nnrat.ring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- equiv [l r]
  (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- m [l r] (ring/rmul l r))
(defn- p [l r] (ring/radd l r))

;; product-only cases, proved through prove-product-equiv
(def cases
  [{:name 'nnringtest/assoc :vars '[a b c]
    :lhs (m (m 'a 'b) 'c) :rhs (m 'a (m 'b 'c))}
   {:name 'nnringtest/comm :vars '[a b]
    :lhs (m 'a 'b) :rhs (m 'b 'a)}
   {:name 'nnringtest/four-reorder :vars '[a b c d]
    :lhs (m (m 'a 'b) (m 'c 'd)) :rhs (m (m 'a 'c) (m 'b 'd))}
   {:name 'nnringtest/full-reverse :vars '[a b c d]
    :lhs (m (m 'a 'b) (m 'c 'd)) :rhs (m (m 'd 'c) (m 'b 'a))}
   {:name 'nnringtest/repeats :vars '[a b]
    :lhs (m (m 'a 'a) 'b) :rhs (m (m 'b 'a) 'a)}
   {:name 'nnringtest/single :vars '[a]
    :lhs 'a :rhs 'a}
   {:name 'nnringtest/degree5 :vars '[a b c d e]
    :lhs (m (m 'a (m 'b 'c)) (m 'd 'e))
    :rhs (m (m 'e 'd) (m 'c (m 'b 'a)))}
   ;; the swap the signed layer needs: (p*q)*r ~ (p*r)*q
   {:name 'nnringtest/swap-outer :vars '[p q r]
    :lhs (m (m 'p 'q) 'r) :rhs (m (m 'p 'r) 'q)}])

;; full semiring cases, proved through prove-equiv
(def sum-cases
  [{:name 'nnringtest/add-comm :vars '[a b]
    :lhs (p 'a 'b) :rhs (p 'b 'a)}
   {:name 'nnringtest/add-assoc :vars '[a b c]
    :lhs (p (p 'a 'b) 'c) :rhs (p 'a (p 'b 'c))}
   {:name 'nnringtest/add-four-reorder :vars '[a b c d]
    :lhs (p (p 'a 'b) (p 'c 'd)) :rhs (p (p 'a 'c) (p 'b 'd))}
   {:name 'nnringtest/distribute-left :vars '[a b c]
    :lhs (m 'a (p 'b 'c)) :rhs (p (m 'a 'b) (m 'a 'c))}
   {:name 'nnringtest/distribute-right :vars '[a b k]
    :lhs (m (p 'a 'b) 'k) :rhs (p (m 'a 'k) (m 'b 'k))}
   {:name 'nnringtest/foil :vars '[a b c d]
    :lhs (m (p 'a 'b) (p 'c 'd))
    :rhs (p (p (m 'a 'c) (m 'b 'c)) (p (m 'a 'd) (m 'b 'd)))}
   ;; the eight-monomial shape behind signed multiplicative associativity
   {:name 'nnringtest/eight-monomials :vars '[pa na pb nb pc nc]
    :lhs (p (p (m (m 'pa 'pb) 'pc) (m (m 'na 'nb) 'pc))
            (p (m (m 'pa 'nb) 'nc) (m (m 'na 'pb) 'nc)))
    :rhs (p (p (m 'pa (m 'pb 'pc)) (m 'pa (m 'nb 'nc)))
            (p (m 'na (m 'pb 'nc)) (m 'na (m 'nb 'pc))))}
   ;; a compound one: (a+b)*(c+d)*(e+f) fully expanded and reordered
   {:name 'nnringtest/triple-product :vars '[a b c d e f]
    :lhs (m (m (p 'a 'b) (p 'c 'd)) (p 'e 'f))
    :rhs (p (p (p (m 'f (m 'd 'b)) (m 'e (m 'c 'a)))
               (p (m 'f (m 'c 'a)) (m 'e (m 'd 'a))))
            (p (p (m 'f (m 'd 'a)) (m 'e (m 'c 'b)))
               (p (m 'f (m 'c 'b)) (m 'e (m 'd 'b)))))}])

(defn- case->spec [{:keys [name vars lhs rhs]}]
  (let [bindings (mapv (fn [v] [v nnrat]) vars)]
    {:name name :universes []
     :type (function/forall bindings (equiv lhs rhs))
     :value (function/lam bindings (:proof (ring/prove-product-equiv lhs rhs)))}))

(defn- sum-case->spec [{:keys [name vars lhs rhs]}]
  (let [bindings (mapv (fn [v] [v nnrat]) vars)]
    {:name name :universes []
     :type (function/forall bindings (equiv lhs rhs))
     :value (function/lam bindings (:proof (ring/prove-equiv lhs rhs)))}))

(def all-specs
  (into (mapv case->spec cases) (mapv sum-case->spec sum-cases)))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (support/extend-with (ring/extend-environment (:environment c))
                           :nnrat-ring-test all-specs))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest nnrat-ring-normalizer-emits-axiom-free-proofs
  (let [env @checked-environment
        ids (support/spec-ids env all-specs)]
    (is (= (into (set (map :name cases)) (map :name sum-cases))
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))

;; the tactic must refuse non-identities rather than emit a false proof
(deftest nnrat-ring-rejects-non-identities
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-product-equiv (m 'a 'b) (m 'a 'c))))
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-equiv (p 'a 'a) 'a)))
  (is (thrown? clojure.lang.ExceptionInfo
               (ring/prove-equiv (m 'a (p 'b 'c)) (p (m 'a 'b) 'c)))))
