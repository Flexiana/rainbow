(ns rainbow.math.sets.finset.range-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.range :as finset-range]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (finset-range/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest range-definitions-are-reducible-axiom-free-data
  (let [checked-environment @checked-environment
        ids (finset-range/definition-ids checked-environment)]
    (is (= #{'setlike/membership 'finset/setlike
             'order/less-than 'order/less-or-equal 'nat/at-most
             'order/preorder-from-partial 'finset/partial-order
             'order/monotone 'list/nat-range 'finset/range}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration checked-environment id)]
        (is (= :definition (:rainbow/kind declaration)) (str name))
        (is (= :reducible (:rainbow/transparency declaration)) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (kernel-checked? checked-environment id) (str name))))))

(deftest range-laws-are-axiom-free-proof-data
  (let [checked-environment @checked-environment
        ids (finset-range/theorem-ids checked-environment)]
    (is (= #{'nat/member-range-successor-add
             'nat/below-member-range
             'finset/member-range-equivalent-below
             'finset/exists-nat-subset-range
             'nat/not-strictly-below-self
             'finset/not-member-range-self
             'finset/member-range-proposition-equality
             'finset/range-subset-of-at-most
             'finset/at-most-of-range-subset
             'finset/range-subset-equivalent-at-most
             'finset/range-monotone}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
