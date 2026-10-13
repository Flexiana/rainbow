(ns rainbow.math.rational.nnrat.map-sum-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.math.rational.nnrat.weighted-map-sum-distance :as weighted]
            [rainbow.math.milestone-support :as support]
            [rainbow.fixtures.nnrat-sum-distance-induction :as independent]
            [rainbow.math.rational.nnrat.map-sum-distance :as target]))

(def checked-environment
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp))
        (throw (ex-info "D63 replay failed" {:status (:status cp)})))
      (weighted/extend-environment (target/extend-environment (:environment cp))))))

(deftest finite-sum-distance-theorems-are-checked-and-axiom-free
  (let [env @checked-environment]
    (doseq [[name id] (merge (target/theorem-ids env) (weighted/theorem-ids env))]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :theorem (:rainbow/kind d)))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))

(defn- c [name] (f/const* name []))
(defn- app [name & xs] (apply f/app (c name) xs))
(defn- numeral [n] (nth (iterate #(app 'data/succ %) (c 'data/zero)) n))
(defn- rational [n d] (app 'nnrat/make (numeral n) (numeral (dec d))))
(def nat (c 'data/Nat))
(defn- items [xs]
  (reduce (fn [tail x] (f/app (f/const* 'data/cons [[:succ [:zero]]]) nat (numeral x) tail))
          (f/app (f/const* 'data/nil [[:succ [:zero]]]) nat) (reverse xs)))
(defn- constant [x] (f/lam [['i nat]] x))
(defn- sum [mapping xs]
  (f/app (f/const* 'nnrat/map-sum [[:zero]]) nat mapping xs))
(defn- core [env expression]
  (let [result (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Instance failed elaboration" result)))
    (:term result)))

(deftest finite-sum-distance-empty-duplicate-and-quotient-instances
  (let [env @checked-environment]
    (doseq [[a b xs] [[(rational 1 1) (rational 0 1) []]
                      [(rational 1 2) (rational 2 4) [0]]
                      [(rational 1 1) (rational 0 1) [0 0]]]]
      (let [left (constant a) right (constant b) source (items xs)
            proof (f/app (f/const* 'nnrat/map-sum-distance-bound [[:zero]]) nat left right source)
            distances (constant (app 'nnrat/distance a b))
            statement (app 'nnrat/at-most
                           (app 'nnrat/distance (sum left source) (sum right source))
                           (sum distances source))]
        (is (= :checked (:status (kernel/check env (core env proof) (core env statement) #{}))))))))

(deftest finite-sum-distance-cannot-drop-the-error-budget
  (let [env @checked-environment
        left (constant (rational 1 1)) right (constant (rational 0 1)) source (items [0])
        proof (f/app (f/const* 'nnrat/map-sum-distance-bound [[:zero]]) nat left right source)
        false-statement (app 'nnrat/at-most
                             (app 'nnrat/distance (sum left source) (sum right source))
                             (c 'nnrat/zero))]
    (is (= :rejected (:status (kernel/check env (core env proof) (core env false-statement) #{}))))))

(deftest weighted-sum-distance-handles-zero-and-unnormalized-weights
  (let [env @checked-environment]
    (doseq [[w a b indexes]
            [[(rational 0 1) (rational 1 1) (rational 0 1) [0]]
             [(rational 2 1) (rational 1 1) (rational 0 1) [0 0]]
             [(rational 1 2) (rational 1 2) (rational 2 4) [0]]
             [(rational 1 1) (rational 1 1) (rational 0 1) []]]]
      (let [left (constant a) right (constant b) weight (constant w)
            source (items indexes)
            proof (f/app (f/const* 'nnrat/weighted-map-sum-distance-bound [[:zero]])
                         nat left right weight source)
            statement (app 'nnrat/at-most
                           (app 'nnrat/distance
                                (sum (constant (app 'nnrat/multiply w a)) source)
                                (sum (constant (app 'nnrat/multiply w b)) source))
                           (sum (constant (app 'nnrat/multiply w (app 'nnrat/distance a b))) source))]
        (is (= :checked (:status (kernel/check env (core env proof) (core env statement) #{}))))))))

(deftest cancellation-does-not-give-an-equality-of-distances
  ;; left = [0,1], right = [1/2,1/2]: distance of sums is 0,
  ;; whereas sum of distances is 1. The theorem is an inequality.
  (let [env @checked-environment
        left (f/lam [['i nat]] (app 'nnrat/make 'i (numeral 0)))
        right (constant (rational 1 2)) source (items [0 1])
        distances (f/lam [['i nat]] (app 'nnrat/distance (f/app left 'i) (f/app right 'i)))
        proof (f/app (f/const* 'nnrat/map-sum-distance-bound [[:zero]]) nat left right source)
        lhs (app 'nnrat/distance (sum left source) (sum right source))
        rhs (sum distances source)]
    (is (= :checked (:status (kernel/check env (core env proof) (core env (app 'nnrat/at-most lhs rhs)) #{}))))
    (is (= :rejected (:status (kernel/check env (core env proof) (core env (app 'nnrat/equivalent lhs rhs)) #{}))))))

(deftest independent-proofs-have-the-same-formal-type
  (let [env (support/add-spec @checked-environment :independent-proof-cross-check
                              independent/map-sum-distance-bound-spec)
        canonical-id (environment/resolve-id env 'nnrat/map-sum-distance-bound)
        alternative-id (environment/resolve-id env 'test/nnrat-map-sum-distance-bound-by-induction)
        canonical (environment/declaration env canonical-id)
        alternative (environment/declaration env alternative-id)]
    (is (some? canonical-id))
    (is (some? alternative-id))
    (is (= (:rainbow/type canonical) (:rainbow/type alternative)))
    (is (not= (:rainbow/value canonical) (:rainbow/value alternative)))
    (is (= :checked (:status (kernel/check env (:rainbow/value alternative) (:rainbow/type canonical) #{'u}))))
    (is (= :checked (:status (kernel/check env (:rainbow/value canonical) (:rainbow/type alternative) #{'u}))))
    (is (= #{} (kernel/axioms env canonical-id)))
    (is (= #{} (kernel/axioms env alternative-id)))))
