(ns rainbow.math.rational.signed.additive-distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.additive-distance :as distance]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (distance/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest signed-additive-distance-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (distance/definition-ids env)
        theorems (distance/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'signed/subtract-at-most-of-additive-upper
             'signed/distance-at-most-of-additive-closeness
             'signed/additive-upper-of-subtract-at-most
             'signed/additive-closeness-of-distance-at-most}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
