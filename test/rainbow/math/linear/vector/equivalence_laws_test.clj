(ns rainbow.math.linear.vector.equivalence-laws-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]
            [rainbow.math.linear.vector.equivalence-laws :as laws]))

(defn- extend-if-missing [checked-environment alias extension]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (extension checked-environment)))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/signed-equivalence-laws/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Signed-equivalence checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          (extend-if-missing 'vector/negate finite-vector/extend-environment)
          (extend-if-missing 'vector/equivalent
                             vector-equivalence/extend-environment)
          laws/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest vector-equivalence-laws-are-general-native-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (laws/theorem-ids checked-environment)]
    (is (= #{'vector/equivalent-reflexive
             'vector/equivalent-symmetric
             'vector/map-respects-equivalence
             'vector/negate-respects-equivalence
             'vector/negate-involutive}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest malformed-vector-equivalence-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment 'vector/negate-respects-equivalence)
        theorem (environment/declaration checked-environment theorem-id)
        trivial-id
        (environment/resolve-id checked-environment 'proposition/trivial)
        result (kernel/check checked-environment [:const trivial-id []]
                             (:rainbow/type theorem)
                             (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
