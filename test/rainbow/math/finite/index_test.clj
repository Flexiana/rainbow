(ns rainbow.math.finite.index-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.index :as index]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (index/extend-environment (:environment checkpoint)))))

(defn- checked? [env alias]
  (let [id (environment/resolve-id env alias)
        declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest structural-bounded-indices-are-kernel-checked-and-axiom-free
  (let [env @checked-environment]
    (is (some? (index/block-id env)))
    (is (= #{'finite/Index 'finite/index-last 'finite/index-weaken
             'finite/index-enumeration 'finite/index-decide-equality
             'finite/index-finset}
           (set (keys (index/definition-ids env)))))
    (is (= #{'finite/index-weaken-injective
             'finite/index-decide-equality-reflexive-true
             'finite/index-equality-implies-decide-equality-true
             'finite/index-decide-equality-true-sound
             'finite/index-last-different-from-weaken
             'finite/index-weaken-membership-reflects
             'finite/index-last-not-member-map-weaken
             'finite/index-map-weaken-no-duplicates
             'finite/index-enumeration-no-duplicates
             'finite/index-successor-cases
             'finite/index-enumeration-covers
             'finite/certified-index-equality
             'finite/index-exhaustive-carrier}
           (set (keys (index/theorem-ids env)))))
    (doseq [alias (concat (keys (index/definition-ids env))
                          (keys (index/theorem-ids env)))]
      (is (checked? env alias) (str alias))
      (is (= #{} (kernel/axioms env (environment/resolve-id env alias)))
          (str alias)))))
