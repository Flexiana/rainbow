(ns rainbow.math.rational.signed.lp-objective-negate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-objective-negate :as sense]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (-> (:environment r) sense/extend-environment decide/extend-environment))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [value target universes]
  (let [r (kernel/check @env (core! value) (core! target) universes)]
    (select-keys r [:status :error])))

(deftest generic-sense-theorems-recheck-axiom-free
  (doseq [[name id] (sense/theorem-ids @env)]
    (let [d (environment/declaration @env id)
          r (kernel/check @env (:rainbow/value d) (:rainbow/type d)
                          (set (:rainbow/universes d)))]
      (println "LP-SENSE-THEOREM" name id (:status r) (kernel/axioms @env id))
      (is (some? id))
      (is (= :checked (:status r)))
      (is (= #{} (kernel/axioms @env id))))))

(deftest original-order-premise-is-not-the-lower-bound-proof
  (let [s sense/negated-objective-bound-to-lower-spec
        r (check (assoc (:value s) 2 'ordered) (:type s) #{'u})]
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (get-in r [:error :error/category])))))

(deftest empty-repeated-signed-and-false-lower-bounds
  (doseq [[cs xs indices lower expected valid?]
          [[[1] [1] [] 0 0 true]
           [[1 2] [2 1] [0 1 1] 5 6 true]
           [[2 -3] [1 2] [0 1 1] -11 -10 true]
           [[1 2] [2 1] [0 1 1] 7 6 false]]]
    (let [mapping (fn [v] (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal v)))
          c (mapping cs) x (mapping xs)
          index-list (reduce (fn [tail i]
                       (f/app (f/const* 'data/cons [[:succ [:zero]]]) lp/nat (#'lp/numeral i) tail))
                     (f/app (f/const* 'data/nil [[:succ [:zero]]]) lp/nat) (reverse indices))
          products (f/lam [['i lp/nat]]
                          (app 'signed/multiply (app 'signed/negate (f/app c 'i)) (f/app x 'i)))
          lhs (poly 'signed/map-sum lp/nat products index-list)
          rhs (app 'signed/negate (#'lp/signed-literal lower))
          proof (poly 'signed/lp-negated-objective-bound-to-lower
                      lp/nat c x index-list (#'lp/signed-literal lower) (#'lp/decided-at-most lhs rhs))
          original-products (f/lam [['i lp/nat]]
                                   (app 'signed/multiply (f/app c 'i) (f/app x 'i)))
          original-sum (poly 'signed/map-sum lp/nat original-products index-list)
          lower-term (#'lp/signed-literal lower)
          expected-term (#'lp/signed-literal expected)
          raw-target (app 'signed/at-most lower-term original-sum)
          target (app 'signed/at-most lower-term expected-term)
          transported (app 'signed/at-most-respects-equivalence
                           lower-term lower-term original-sum expected-term
                           (app 'signed/equivalent-reflexive lower-term)
                           (#'lp/computed-equivalence original-sum expected-term) proof)
          raw (check proof raw-target #{})
          r (check transported target #{})]
      (println "LP-SENSE-CASE" indices lower expected :formal (:status raw)
               :literal (:status r) (get-in r [:error :error/category]))
      (is (= (if valid? :checked :rejected) (:status raw)))
      (is (= (if valid? :checked :rejected) (:status r)))
      (when-not valid?
        (is (= :kernel/type-mismatch (get-in raw [:error :error/category])))
        (is (= :kernel/type-mismatch (get-in r [:error :error/category]))))
      (when (neg? expected)
        ;; The original sum is represented as 2-12, not the literal 0-10.
        ;; Relabelling its proof without quotient transport must not pass.
        (let [untransported (check proof target #{})]
          (println "LP-SENSE-UNTRANSPORTED" (:status untransported)
                   (get-in untransported [:error :error/category]))
          (is (= :rejected (:status untransported)))
          (is (= :kernel/type-mismatch (get-in untransported [:error :error/category]))))))))
