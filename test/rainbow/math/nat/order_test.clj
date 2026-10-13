(ns rainbow.math.nat.order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.order :as nat-order]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          finset-data/extend-environment
          finite-expectation/extend-environment
          nat-order/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest constructive-order-laws-are-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (nat-order/theorem-ids checked-environment)]
    (is (= #{'nat/at-most-reflexive 'nat/at-most-transitive
             'nat/at-most-successor
             'nat/add-left-monotone 'nat/add-right-monotone
             'nat/add-monotone 'nat/multiply-add-left
             'nat/multiply-right-monotone 'nat/multiply-left-monotone
             'list/nat-map-sum-monotone
             'probability/expectation-monotone}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
