(ns rainbow.math.nat.divisibility-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.divisibility :as divisibility]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (divisibility/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest natural-divisibility-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (divisibility/definition-ids env)]
    (is (= #{'nat/divides} (set (keys definitions))))
    (is (empty? (divisibility/theorem-ids env)))
    (doseq [[name id] definitions]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
