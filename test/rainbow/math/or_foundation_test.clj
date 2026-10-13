(ns rainbow.math.or-foundation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.or-foundation :as foundation]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-wide/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-74 checkpoint rejected" {:checkpoint checkpoint})))
      (foundation/extend-environment (:environment checkpoint)))))

(deftest product-diagonal-injectivity-is-axiom-free-proof-data
  (let [environment @checked-environment
        id (environment/resolve-id
            environment 'function/product-diagonal-injective)
        declaration (environment/declaration environment id)]
    (is (string? id))
    (is (= :theorem (:rainbow/kind declaration)))
    (is (= #{} (kernel/axioms environment id)))
    (is (= :checked
           (:status (kernel/check environment
                                  (:rainbow/value declaration)
                                  (:rainbow/type declaration)
                                  #{'u}))))))
