(ns rainbow.algorithms.proofs.ahof.kmeans-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kmeans :as kmeans]
            [rainbow.algorithms.reference.kmeans :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kmeans/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kmeans-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kmeans/definition-ids checked-environment)
        theorems (kmeans/theorem-ids checked-environment)]
    (is (= #{'kmeans/assign} (set (keys definitions))))
    (is (= #{'kmeans/assigns-to-nearest 'kmeans/assigns-to-second-when-nearer
             'kmeans/assigned-is-nearest}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kmeans
  (is (= 0 (executable/assign 2 0 7 1)))
  (is (= 1 (executable/assign 9 0 3 1)))
  (is (= 0 (executable/nearest-centroid [0 10] 3)))
  ;; two clusters around 1 and 10 converge to those means
  (is (= [1 10] (executable/kmeans [0 1 2 9 10 11] [3 8] 5))))
