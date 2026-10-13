(ns rainbow.math.rational.signed.decide-equivalence-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-equivalence :as decide]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(defn- app [f & args] (apply function/app f args))

(defn- nat [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (nat (dec n)))))

(defn- nnrat
  "`nnrat n d` denotes n/(d+1); the representation stores the denominator
  predecessor."
  [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       (nat numerator) (nat denominator-predecessor)))

(defn- signed-value [positive negative]
  (app (function/const* 'signed/make []) positive negative))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- decide-equivalent [left right]
  (app (function/const* 'signed/decide-equivalent []) left right))
(defn- reflexive-true []
  (app (function/const* 'equality/reflexive [type-level]) bool true-value))

(def zero (nnrat 0 0))
(def one-half (signed-value (nnrat 1 1) zero))
(def two-fourths (signed-value (nnrat 2 3) zero))
(def three-fourths (signed-value (nnrat 3 3) zero))
(def minus-two-a (signed-value (nnrat 1 0) (nnrat 3 0)))
(def minus-two-b (signed-value (nnrat 2 0) (nnrat 4 0)))

(def cases
  [{:name 'decideeq/equal-fractions
    :left one-half :right two-fourths}
   {:name 'decideeq/equal-negative-pairs
    :left minus-two-a :right minus-two-b}
   {:name 'decideeq/reflexive
    :left three-fourths :right three-fourths}])

(defn- case->spec [{:keys [name left right]}]
  {:name name :universes []
   :type (equivalent left right)
   :value
   (app (function/const* 'signed/decide-equivalent-true-sound [])
        left right (reflexive-true))})

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (decide/extend-environment (:environment checkpoint))
       :signed-decide-equivalence-test
       (mapv case->spec cases)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-equivalence-decision-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (decide/definition-ids env) (decide/theorem-ids env))]
    (is (= #{'signed/decide-equivalent
             'signed/decide-equivalent-true-sound}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest equivalent-signed-values-are-discharged-by-computation
  (let [env @checked-environment
        ids (support/spec-ids env (mapv case->spec cases))]
    (is (= (set (map :name cases)) (set (keys ids))))
    (doseq [[name id] ids]
      (testing (str name)
        (is (checked? env id))
        (is (= #{} (kernel/axioms env id)))))))

(deftest an-unequal-comparison-is-refused-by-the-kernel
  (let [env @checked-environment
        bogus
        (app (function/const* 'signed/decide-equivalent-true-sound [])
             one-half three-fourths (reflexive-true))
        value (:term (elaborate/core-expression env bogus))
        claimed (:term (elaborate/core-expression
                        env (equivalent one-half three-fourths)))
        result (kernel/check env value claimed #{})]
    (is (not= :checked (:status result))
        "the kernel must refuse a certificate for unequal signed values")
    (is (= :kernel/type-mismatch (get-in result [:error :error/category])))))
