(ns rainbow.math.rational.signed.max-three-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.max-three :as max-three]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (max-three/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status (kernel/check env (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))))

(deftest fixed-three-maximum-has-an-axiom-free-optimality-certificate
  (let [env @checked-environment]
    (testing "the unrolled three-candidate fold is kernel-checked"
      (is (= #{'signed/max-three}
             (set (keys (max-three/definition-ids env)))))
      (doseq [[name id] (max-three/definition-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (testing "all candidates are bounded and the bound is least"
      (is (= #{'signed/max-three-upper-first
               'signed/max-three-upper-second
               'signed/max-three-upper-third
               'signed/max-three-least-upper
               'signed/max-three-is-first-or-second-or-third}
             (set (keys (max-three/theorem-ids env)))))
      (doseq [[name id] (max-three/theorem-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
