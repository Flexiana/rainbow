(ns rainbow.math.linear.matrix.row-length-decider-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.row-length-decider :as decider]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-list [element]
  (app (function/const* 'data/nil [type-level]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [type-level]) element head tail))
(defn- vector-of-length [n]
  (loop [remaining n, result (nil-list signed)]
    (if (zero? remaining)
      result
      (recur (dec remaining)
             (cons-list signed (function/const* 'signed/zero []) result)))))
(defn- matrix [& rows]
  (reduce (fn [tail row] (cons-list vector-type row tail))
          (nil-list vector-type) (reverse rows)))
(defn- decide [rows values]
  (app (function/const* 'matrix/decide-row-length-compatible [])
       rows values))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))
(defn- reflexive-bool [value]
  (app (function/const* 'equality/reflexive [type-level]) bool value))

(def rectangular-rows (matrix (vector-of-length 2) (vector-of-length 2)))
(def ragged-rows (matrix (vector-of-length 2) (vector-of-length 1)))
(def reference (vector-of-length 2))

(def computation-specs
  [{:name 'matrix-row-length-decider-test/accepts-rectangular
    :universes []
    :type
    (bool-equality
     (decide rectangular-rows reference)
     (function/const* 'data/true []))
    :value (reflexive-bool (function/const* 'data/true []))}
   {:name 'matrix-row-length-decider-test/rejects-ragged
    :universes []
    :type
    (bool-equality
     (decide ragged-rows reference)
     (function/const* 'data/false []))
    :value (reflexive-bool (function/const* 'data/false []))}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (decider/extend-environment (:environment checkpoint))
       :finite-matrix-row-length-decider-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest row-length-decider-is-native-sound-and-axiom-free
  (let [env @checked-environment
        definitions (decider/definition-ids env)
        theorems (decider/theorem-ids env)]
    (is (= #{'matrix/decide-row-length-compatible}
           (set (keys definitions))))
    (is (= #{'nat/decide-equality-true-sound
             'matrix/decide-row-length-compatible-true-sound
             'nat/decide-equality-reflexive-true
             'nat/equality-implies-decide-equality-true
             'boolean/and-true-introduction
             'matrix/row-length-compatible-implies-decide-true
             'matrix/decide-row-length-compatible-true-implies-compatible
             'matrix/decide-row-length-compatible-true-implies-rectangular}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest checker-computes-on-rectangular-and-ragged-matrices
  (let [env @checked-environment]
    (doseq [spec computation-specs]
      (let [id (environment/resolve-id env (:name spec))]
        (is (some? id) (str (:name spec)))
        (is (checked? env id) (str (:name spec)))
        (is (= #{} (kernel/axioms env id)) (str (:name spec)))))))
