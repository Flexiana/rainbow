(ns rainbow.math.linear.vector.uniform-clamp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.uniform-clamp :as clamp]))

(def type-level [:succ [:zero]])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
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
(defn- vector [& components]
  (reduce
   (fn [tail component]
     (app (function/const* 'data/cons [type-level]) signed component tail))
   (app (function/const* 'data/nil [type-level]) signed)
   (reverse components)))
(defn- uniform-clamp [lower upper values]
  (app (function/const* 'vector/uniform-clamp []) lower upper values))
(defn- eq-vector [left right]
  (function/equality type-level vector-type left right))
(defn- reflexive-vector [value]
  (app (function/const* 'equality/reflexive [type-level]) vector-type value))

(def lower (signed-value 0 1))
(def upper (signed-value 2 0))
(def below (signed-value 0 3))
(def inside (signed-value 1 0))
(def above (signed-value 4 0))
(def input (vector below inside above))
(def output (vector lower inside upper))

(def computation-specs
  [{:name 'vector-clamp-test/three-regions :universes []
    :type (eq-vector (uniform-clamp lower upper input) output)
    :value (reflexive-vector output)}
   {:name 'vector-clamp-test/empty :universes []
    :type (eq-vector
           (uniform-clamp lower upper
                          (app (function/const* 'data/nil [type-level]) signed))
           (app (function/const* 'data/nil [type-level]) signed))
    :value
    (reflexive-vector
     (app (function/const* 'data/nil [type-level]) signed))}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (clamp/extend-environment (:environment checkpoint))
       :vector-uniform-clamp-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-uniform-clamp-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (clamp/definition-ids env)
        theorems (clamp/theorem-ids env)]
    (is (= #{'vector/uniform-clamp 'vector/in-band}
           (set (keys definitions))))
    (is (= #{'vector/in-band-empty 'vector/in-band-cons
             'vector/uniform-clamp-in-band
             'vector/uniform-clamp-respects-equivalence
             'vector/uniform-clamp-preserves-in-band
             'vector/uniform-clamp-idempotent}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest vector-uniform-clamp-computes-componentwise
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= (set (map :name computation-specs)) (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
