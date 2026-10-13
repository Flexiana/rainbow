(ns rainbow.algorithms.proofs.ahof.knn-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.knn :as knn]
            [rainbow.algorithms.reference.knn :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          knn/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest knn-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (knn/definition-ids checked-environment)
        theorems (knn/theorem-ids checked-environment)]
    (is (= #{'knn/predict} (set (keys definitions))))
    (is (= #{'knn/predicts-plurality-class 'knn/plurality-dominates-zero
             'knn/plurality-dominates-two}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-knn
  (is (= 1 (executable/knn-predict [2 4 1])))
  ;; 1-D points, k=3, class of query 5: nearest are 4,6,3 with labels 0,0,1 -> 0
  (is (= 0 (executable/classify 3 2 [[1 1] [3 1] [4 0] [6 0] [10 1]]
                                (fn [a b] (abs (- a b))) 5))))
