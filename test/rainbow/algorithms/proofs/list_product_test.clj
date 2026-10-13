(ns rainbow.algorithms.proofs.list-product-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.list-product :as list-product]
            [rainbow.algorithms.reference.list-product :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          list-product/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest list-product-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (list-product/definition-ids checked-environment)
        theorems (list-product/theorem-ids checked-environment)]
    (is (= #{'list-product/product} (set (keys definitions))))
    (is (= #{'list-product/product-empty 'list-product/product-cons
             'list-product/product-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-list-product-reduces
  (is (= 12 (executable/list-product [2 3 2])))
  (is (= 1 (executable/list-product [])))
  ;; joint probability of independent events 1/2, 1/3
  (is (= 1/6 (executable/joint-probability [1/2 1/3]))))
