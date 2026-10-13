(ns rainbow.math.linear.vector.projected-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.projected-gradient :as projected]))

(def type-level [:succ [:zero]])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
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
(defn- vector-of [& components]
  (reduce
   (fn [tail component]
     (app (function/const* 'data/cons [type-level]) signed component tail))
   (app (function/const* 'data/nil [type-level]) signed)
   (reverse components)))
(defn- projected-step [lower upper rate point gradient]
  (app (function/const* 'optimization/vector-projected-step [])
       lower upper rate point gradient))
(defn- in-band [lower upper values]
  (app (function/const* 'vector/in-band []) lower upper values))
(defn- reflexive-true []
  (app (function/const* 'equality/reflexive [type-level])
       bool true-value))
(defn- at-most-proof [left right]
  (app (function/const* 'signed/decide-at-most-true-sound [])
       left right (reflexive-true)))

(def lower (signed-value 0 1))
(def upper (signed-value 1 0))
(def rate (whole 1))
(def point
  (vector-of (signed-value 2 0)
             (signed-value 0 0)
             (signed-value 0 2)))
(def gradient
  (vector-of (signed-value 1 0)
             (signed-value 0 2)
             (signed-value 0 1)))

(def computation-specs
  [{:name 'vector-projected-test/three-dimensional-step-is-feasible
    :universes []
    :type (in-band lower upper
                   (projected-step lower upper rate point gradient))
    :value
    (app (function/const* 'optimization/vector-projected-step-in-band [])
         lower upper (at-most-proof lower upper)
         rate point gradient)}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (projected/extend-environment (:environment checkpoint))
       :vector-projected-gradient-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-projected-gradient-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (projected/definition-ids env)
        theorems (projected/theorem-ids env)]
    (is (= #{'optimization/vector-projected-step}
           (set (keys definitions))))
    (is (= #{'optimization/vector-projected-step-unfold
             'optimization/vector-projected-step-in-band
             'optimization/vector-projected-step-reprojection
             'optimization/vector-projected-step-monotone}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest three-dimensional-step-has-a-checked-feasibility-certificate
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= #{'vector-projected-test/three-dimensional-step-is-feasible}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
