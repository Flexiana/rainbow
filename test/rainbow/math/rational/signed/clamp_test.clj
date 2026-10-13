(ns rainbow.math.rational.signed.clamp-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.clamp :as clamp]))

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
(defn- clamp-value [lower upper value]
  (app (function/const* 'signed/clamp []) lower upper value))
(defn- eq-signed [left right]
  (function/equality type-level signed left right))
(defn- reflexive-signed [value]
  (app (function/const* 'equality/reflexive [type-level]) signed value))

(def lower (signed-value 0 1)) ; -1
(def upper (signed-value 2 0)) ;  2
(def below (signed-value 0 3)) ; -3
(def inside (signed-value 1 0))
(def above (signed-value 4 0))

(def computation-specs
  [{:name 'signed-clamp-test/saturates-lower :universes []
    :type (eq-signed (clamp-value lower upper below) lower)
    :value (reflexive-signed lower)}
   {:name 'signed-clamp-test/preserves-inside :universes []
    :type (eq-signed (clamp-value lower upper inside) inside)
    :value (reflexive-signed inside)}
   {:name 'signed-clamp-test/saturates-upper :universes []
    :type (eq-signed (clamp-value lower upper above) upper)
    :value (reflexive-signed upper)}])

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (support/extend-with
       (clamp/extend-environment (:environment checkpoint))
       :signed-clamp-test computation-specs))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-clamp-is-universal-native-and-axiom-free
  (let [env @checked-environment
        definitions (clamp/definition-ids env)
        theorems (clamp/theorem-ids env)]
    (is (= #{'signed/clamp} (set (keys definitions))))
    (is (= #{'signed/clamp-lower 'signed/clamp-upper
             'signed/clamp-in-band 'signed/clamp-monotone
             'signed/clamp-respects-equivalence
             'signed/clamp-below 'signed/clamp-above}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest signed-clamp-computes-all-three-regions
  (let [env @checked-environment
        ids (support/spec-ids env computation-specs)]
    (is (= (set (map :name computation-specs)) (set (keys ids))))
    (doseq [[name id] ids]
      (testing (str name)
        (is (checked? env id))
        (is (= #{} (kernel/axioms env id)))))))
