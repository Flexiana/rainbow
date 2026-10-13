(ns rainbow.math.linear.vector.pointwise-order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.pointwise-order :as pointwise]))

(def type-level [:succ [:zero]])
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
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- reflexive-true []
  (app (function/const* 'equality/reflexive [type-level])
       bool true-value))
(defn- at-most-proof [left right]
  (app (function/const* 'signed/decide-at-most-true-sound [])
       left right (reflexive-true)))

(def left (vector-of (signed-value 0 1) (signed-value 1 0)))
(def right (vector-of (signed-value 0 0) (signed-value 2 0)))

(def computation-specs
  [{:name 'vector-order-test/two-components :universes []
    :type (vector-at-most left right)
    :value
    (let [truth (function/const* 'proposition/truth [])
          trivial (function/const* 'proposition/trivial [])
          conjunction (fn [a b]
                        (app (function/const* 'proposition/conjunction []) a b))
          conjoin (fn [a b pa pb]
                    (app (function/const* 'proposition/conjoin []) a b pa pb))
          at-most (fn [a b]
                    (app (function/const* 'signed/at-most []) a b))
          first-left (signed-value 0 1)
          first-right (signed-value 0 0)
          second-left (signed-value 1 0)
          second-right (signed-value 2 0)]
      (conjoin
       (at-most first-left first-right)
       (conjunction (at-most second-left second-right) truth)
       (at-most-proof first-left first-right)
       (conjoin (at-most second-left second-right) truth
                (at-most-proof second-left second-right) trivial)))}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (pointwise/extend-environment (:environment checkpoint))
       :vector-pointwise-order-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-pointwise-order-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (pointwise/definition-ids env)
        theorems (pointwise/theorem-ids env)]
    (is (= #{'vector/at-most} (set (keys definitions))))
    (is (= #{'vector/at-most-empty 'vector/at-most-cons
             'vector/at-most-reflexive
             'vector/uniform-clamp-monotone}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest vector-pointwise-order-computes
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= #{'vector-order-test/two-components} (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
