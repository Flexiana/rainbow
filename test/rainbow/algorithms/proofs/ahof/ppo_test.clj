(ns rainbow.algorithms.proofs.ahof.ppo-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.ppo :as ppo]
            [rainbow.algorithms.reference.ppo :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ppo/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest ppo-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ppo/definition-ids checked-environment)
        theorems (ppo/theorem-ids checked-environment)]
    (is (= #{'ppo/nnrat-min 'ppo/nnrat-max 'ppo/clip}
           (set (keys definitions))))
    (is (= #{'ppo/clips-above-to-hi 'ppo/clips-below-to-lo 'ppo/passes-in-band}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-ppo-clips
  (is (= 5/4 (executable/ppo-clip 3/2 3/4 5/4)))
  (is (= 3/4 (executable/ppo-clip 1/2 3/4 5/4)))
  (is (= 1 (executable/ppo-clip 1 3/4 5/4)))
  ;; clipped surrogate at r=3/2, A=2, eps=1/4: min(3, 5/4*2=5/2) = 5/2
  (is (= 5/2 (executable/clipped-surrogate 3/2 2 1/4))))
