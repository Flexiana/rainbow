(ns rainbow.math.nat.metric-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.distance :as nat-distance]
            [rainbow.math.nat.metric :as nat-metric]
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
          nat-order/extend-environment
          nat-distance/extend-environment
          nat-metric/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest natural-distance-is-a-constructive-ordered-metric
  (let [checked-environment @checked-environment
        ids (nat-metric/theorem-ids checked-environment)]
    (is (= #{'nat/distance-first-bound
             'nat/distance-upper-add
             'nat/distance-triangle}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
