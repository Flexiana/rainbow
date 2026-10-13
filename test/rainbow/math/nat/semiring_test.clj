(ns rainbow.math.nat.semiring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.semiring :as nat-semiring]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/or-contraction/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "OR contraction checkpoint rejected"
                        {:checkpoint checkpoint})))
      (nat-semiring/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nat-semiring-prerequisites-are-native-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        theorems (nat-semiring/theorem-ids checked-environment)]
    (is (= #{'nat/add-left-cancel
             'nat/multiply-associative
             'nat/multiply-four-reorder
             'nat/multiply-one-right
             'nat/multiply-swap-right
             'nat/multiply-successor-right-cancel}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
