(ns rainbow.math.rational.signed.minmax-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.minmax :as minmax]))

(def type-level [:succ [:zero]])
(def signed (function/const* 'signed/SignedRational []))
(defn- app [f & args] (apply function/app f args))

(defn- nat [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (nat (dec n)))))
(defn- whole [n]
  (app (function/const* 'nnrat/make [])
       (nat n) (function/const* 'data/zero [])))
(defn- signed-value [positive negative]
  (app (function/const* 'signed/make []) (whole positive) (whole negative)))
(defn- minimum [left right]
  (app (function/const* 'signed/min []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- eq-signed [left right]
  (function/equality type-level signed left right))
(defn- reflexive-signed [value]
  (app (function/const* 'equality/reflexive [type-level]) signed value))

(def minus-three (signed-value 0 3))
(def two (signed-value 2 0))

(def computation-specs
  [{:name 'signed-minmax-test/min-true-branch :universes []
    :type (eq-signed (minimum minus-three two) minus-three)
    :value (reflexive-signed minus-three)}
   {:name 'signed-minmax-test/min-false-branch :universes []
    :type (eq-signed (minimum two minus-three) minus-three)
    :value (reflexive-signed minus-three)}
   {:name 'signed-minmax-test/max-true-branch :universes []
    :type (eq-signed (maximum minus-three two) two)
    :value (reflexive-signed two)}
   {:name 'signed-minmax-test/max-false-branch :universes []
    :type (eq-signed (maximum two minus-three) two)
    :value (reflexive-signed two)}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (minmax/extend-environment (:environment checkpoint))
       :signed-minmax-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-minmax-is-universal-native-and-axiom-free
  (let [env @checked-environment
        definitions (minmax/definition-ids env)
        theorems (minmax/theorem-ids env)]
    (is (= #{'signed/min 'signed/max} (set (keys definitions))))
    (is (= #{'signed/min-lower-left 'signed/min-lower-right
             'signed/max-upper-left 'signed/max-upper-right
             'signed/at-most-min 'signed/at-most-max}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest signed-minmax-computes-both-order-branches
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= (set (map :name computation-specs)) (set (keys ids))))
    (doseq [[name id] ids]
      (testing (str name)
        (is (checked? env id))
        (is (= #{} (kernel/axioms env id)))))))
