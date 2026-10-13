(ns rainbow.algorithms.proofs.ahof.simplex-interpolation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.simplex-interpolation :as si]
            [rainbow.algorithms.reference.simplex-interpolation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          si/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest simplex-interpolation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (si/definition-ids checked-environment)
        theorems (si/theorem-ids checked-environment)]
    (is (= #{'simplex-interpolation/interpolate} (set (keys definitions))))
    (is (= #{'simplex-interpolation/interpolate-unfold
             'simplex-interpolation/interpolate-example
             'simplex-interpolation/interpolate-at-vertex}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-simplex-interpolation
  (is (= 13 (executable/interpolate-tri 2 3 1 4 3 1)))
  (is (= 3 (executable/interpolate-tri 1 3 0 4 0 1)))
  ;; Convex barycentric weights (1/2, 1/4, 1/4) over vertex values (4, 8, 12).
  (is (= 7 (executable/interpolate [1/2 1/4 1/4] [4 8 12]))))
