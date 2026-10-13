(ns rainbow.math.rational.signed.minmax-algebra-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.minmax-algebra :as algebra]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (algebra/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-minmax-algebra-is-universal-native-and-axiom-free
  (let [env @checked-environment
        ids (algebra/theorem-ids env)]
    (is (= #{'signed/min-commutative 'signed/max-commutative
             'signed/min-idempotent 'signed/max-idempotent
             'signed/min-monotone 'signed/max-monotone
             'signed/min-associative 'signed/max-associative}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
