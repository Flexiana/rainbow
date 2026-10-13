(ns rainbow.math.rational.signed.decide-order-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(defn- app [f & args] (apply function/app f args))

;; concrete signed literals: signed/make positive-part negative-part
(defn- nat [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (nat (dec n)))))
(defn- whole [n]
  (app (function/const* 'nnrat/make []) (nat n)
       (function/const* 'data/zero [])))
(defn- signed-value [p n]
  (app (function/const* 'signed/make []) (whole p) (whole n)))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- decide-at-most [a b]
  (app (function/const* 'signed/decide-at-most []) a b))
(defn- reflexive-bool []
  (app (function/const* 'equality/reflexive [type-level]) bool true-value))

(def minus-three (signed-value 0 3))
(def two (signed-value 2 0))
(def minus-one (signed-value 0 1))

;; each case asserts a CONCRETE order fact, discharged by reduction:
;; the decision computes, reflexivity witnesses that it computed to true,
;; and soundness turns that into the order fact.
(def cases
  [{:name 'decidetest/negative-below-positive :left minus-three :right two}
   {:name 'decidetest/negative-below-negative :left minus-three :right minus-one}
   {:name 'decidetest/reflexive-on-a-negative :left minus-three :right minus-three}])

(defn- case->spec [{:keys [name left right]}]
  {:name name :universes []
   :type (sle left right)
   :value (app (function/const* 'signed/decide-at-most-true-sound [])
               left right (reflexive-bool))})

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with (decide/extend-environment (:environment checkpoint))
                           :signed-decide-order-test
                           (mapv case->spec cases)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest signed-order-decision-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (decide/definition-ids env) (decide/theorem-ids env))]
    (is (= #{'signed/decide-at-most
             'signed/decide-at-most-true-sound
             'signed/decide-at-most-false-reverse}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest concrete-signed-inequalities-are-discharged-by-computation
  (let [env @checked-environment
        ids (support/spec-ids env (mapv case->spec cases))]
    (is (= (set (map :name cases)) (set (keys ids))))
    (doseq [[name id] ids]
      (testing (str name)
        (is (checked? env id))
        (is (= #{} (kernel/axioms env id)))))))

(deftest a-false-comparison-is-refused-by-the-kernel
  (let [env @checked-environment
        ;; 2 <= -3 is false: the decision computes to false, so the reflexivity
        ;; witness that it computed to true cannot inhabit its type
        bogus (app (function/const* 'signed/decide-at-most-true-sound [])
                   two minus-three (reflexive-bool))
        value (:term (elaborate/core-expression env bogus))
        claimed (:term (elaborate/core-expression env (sle two minus-three)))
        result (kernel/check env value claimed #{})]
    (is (not= :checked (:status result))
        "the kernel must refuse a certificate for a false inequality")
    (is (= :kernel/type-mismatch (get-in result [:error :error/category])))))
