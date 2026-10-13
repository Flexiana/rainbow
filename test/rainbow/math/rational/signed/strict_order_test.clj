(ns rainbow.math.rational.signed.strict-order-test
  "Gate for the signed strict-order foundation: less-than and its intro, at-most projection,
  irreflexivity, and asymmetry, all kernel-checked and axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.strict-order :as strict]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (strict/extend-environment (:environment checkpoint)))))

(deftest strict-order-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (strict/theorem-ids env)]
    (is (= #{'signed/less-than 'signed/less-than-intro 'signed/less-than-implies-at-most
             'signed/less-than-irreflexive 'signed/less-than-asymmetric
             'signed/less-than-transitive 'signed/less-than-of-at-most-of-less-than
             'signed/less-than-of-less-than-of-at-most}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
