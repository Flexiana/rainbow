(ns rainbow.math.logic.infinite-injection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.infinitude-transport :as infinitude-transport]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.infinite-injection :as infinite-injection]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint infinitude-transport/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-79 checkpoint rejected" {:checkpoint checkpoint})))
      (infinite-injection/extend-environment (:environment checkpoint)))))

(deftest injection-transport-is-explicit-classical-proof-data
  (let [environment @checked-environment
        excluded-middle-id
        (environment/resolve-id environment 'logic/excluded-middle)
        ids (infinite-injection/theorem-ids environment)]
    (is (= #{'list/preimage-representatives
             'type/finite-of-injection
             'type/infinite-of-injection}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [declaration (environment/declaration environment id)
            replay (kernel/check environment
                                 (:rainbow/value declaration)
                                 (:rainbow/type declaration)
                                 (set (:rainbow/universes declaration)))]
        (is (= :theorem (:rainbow/kind declaration)) (str name))
        (is (= :checked (:status replay)) (str name))
        (is (= #{excluded-middle-id} (kernel/axioms environment id))
            (str name))))))
