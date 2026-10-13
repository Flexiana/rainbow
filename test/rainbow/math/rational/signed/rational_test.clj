(ns rainbow.math.rational.signed.rational-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.value-of-information :as ahof-d19]
            [rainbow.math.rational.signed.rational :as signed]
            [rainbow.algorithms.reference.value-of-information :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d40-local-search/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D40 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          signed/extend-environment
          ahof-d19/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-rationals-are-native-axiom-free-and-additive
  (let [checked-environment @checked-environment
        definitions (signed/definition-ids checked-environment)
        theorems (signed/theorem-ids checked-environment)]
    (is (= #{'signed/SignedRational 'signed/make 'signed/positive
             'signed/negative 'signed/from-nnrat 'signed/zero 'signed/one
             'signed/add 'signed/negate 'signed/subtract 'signed/equivalent
             'signed/nonnegative}
           (set (keys definitions))))
    (is (= #{'signed/positive-of-make 'signed/negative-of-make
             'signed/subtract-unfold 'signed/equivalent-reflexive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d19-value-of-information-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d19/theorem-ids checked-environment)]
    (is (= #{'ahof-d19/information-never-hurts
             'ahof-d19/voi-equals-quarter
             'ahof-d19/voi-nonnegative
             'ahof-d19/value-of-information-theorem}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-value-of-information-is-exact-and-nonnegative
  (is (= 1/4 (executable/value-of-information 3/4 1/2)))
  (is (true? (executable/information-never-hurts? 3/4 1/2)))
  ;; Information never hurts even when it changes nothing.
  (is (= 0 (executable/value-of-information 1/2 1/2)))
  (is (true? (executable/information-never-hurts? 1/2 1/2))))
