(ns rainbow.math.linear.vector.add-order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.add-order :as order]))

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
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- reflexive-true []
  (app (function/const* 'equality/reflexive [type-level])
       bool true-value))
(defn- at-most-proof [left right]
  (app (function/const* 'signed/decide-at-most-true-sound [])
       left right (reflexive-true)))
(defn- vector-order-proof [left-head right-head left-tail right-tail tail-proof]
  (app (function/const* 'vector/at-most-cons [])
       left-head right-head left-tail right-tail
       (at-most-proof left-head right-head) tail-proof))

(def empty-vector
  (app (function/const* 'data/nil [type-level]) signed))
(def left (vector-of (signed-value 0 1) (signed-value 1 0)))
(def right (vector-of (signed-value 0 0) (signed-value 2 0)))
(def offset (vector-of (signed-value 3 0) (signed-value 0 4)))

(def ordered
  (let [left-one (signed-value 0 1)
        right-one (signed-value 0 0)
        left-two (signed-value 1 0)
        right-two (signed-value 2 0)]
    (vector-order-proof
     left-one right-one
     (vector-of left-two) (vector-of right-two)
     (vector-order-proof
      left-two right-two empty-vector empty-vector
      (function/const* 'proposition/trivial [])))))

(def computation-specs
  [{:name 'vector-add-order-test/two-dimensional-translation :universes []
    :type (vector-at-most (vector-add left offset)
                          (vector-add right offset))
    :value
    (app (function/const* 'vector/add-right-monotone [])
         left right offset ordered)}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (order/extend-environment (:environment checkpoint))
       :vector-add-order-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-add-order-is-native-and-axiom-free
  (let [env @checked-environment
        ids (order/theorem-ids env)]
    (is (= #{'vector/add-right-monotone
             'vector/add-left-monotone
             'vector/add-monotone
             'vector/add-respects-equivalence
             'vector/add-commutative
             'vector/add-associative}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest concrete-vector-translation-preserves-order
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= #{'vector-add-order-test/two-dimensional-translation}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
