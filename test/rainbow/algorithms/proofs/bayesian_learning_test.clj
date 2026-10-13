(ns rainbow.algorithms.proofs.bayesian-learning-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bayesian-learning :as ahof-d11]
            [rainbow.algorithms.proofs.bayesian-learning :as iteration]
            [rainbow.algorithms.reference.bayesian-learning :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d10-maximum-likelihood/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D10 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d11/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bayesian-learning-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'estimation/bayesian-update 'estimation/bayesian-posterior}
           (set (keys definitions))))
    (is (= #{'estimation/bayesian-update-unfold
             'estimation/bayesian-posterior-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d11-bayesian-learning-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d11/theorem-ids checked-environment)]
    (is (= #{'ahof-d11/first-update-is-three-quarters
             'ahof-d11/posterior-is-one
             'ahof-d11/bayesian-learning}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bayesian-learning-folds-likelihoods-through-prior
  ;; Prior 1/2, likelihoods 3/2 then 4/3: the first update gives 1/2 * 3/2 = 3/4,
  ;; and the posterior 3/4 * 4/3 = 1.
  (is (= 3/4 (executable/bayesian-update 1/2 3/2)))
  (is (= 1 (executable/posterior 1/2 [3/2 4/3])))
  ;; The empty data set leaves the prior unchanged.
  (is (= 1/2 (executable/posterior 1/2 []))))
