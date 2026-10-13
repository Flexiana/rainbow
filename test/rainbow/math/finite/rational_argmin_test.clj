(ns rainbow.math.finite.rational-argmin-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-argmin :as argmin]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (argmin/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-rational-argmin-is-native-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (argmin/definition-ids checked-environment)
        theorems (argmin/theorem-ids checked-environment)]
    (is (= #{'decision/nnrat-select-min
             'list/nnrat-argmin-from
             'decision/finite-nnrat-argmin}
           (set (keys definitions))))
    (is (= #{'decision/nnrat-select-min-is-left-or-right
             'decision/nnrat-select-min-bounds-left
             'decision/nnrat-select-min-bounds-right
             'list/nnrat-argmin-from-bounded-by-initial
             'list/nnrat-argmin-from-bounded-by-member
             'list/nnrat-argmin-from-is-initial-or-member
             'decision/finite-nnrat-argmin-is-member
             'decision/finite-nnrat-argmin-dominates}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
