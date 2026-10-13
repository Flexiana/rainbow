(ns rainbow.boolean-and-soundness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.boolean-and :as ba]
            [rainbow.math.logic.interval-membership-sound :as ims]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (-> (:environment c)
          ba/extend-environment
          ims/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest boolean-and-soundness-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (ba/definition-ids env) (ba/theorem-ids env))]
    (is (= #{'boolean/and 'boolean/and-implies-left 'boolean/and-implies-right
             'boolean/and-sound}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))

(deftest interval-membership-soundness-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (ims/definition-ids env) (ims/theorem-ids env))]
    (is (= #{'ims/contains? 'ims/contains-sound} (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
