(ns rainbow.math.sets.image-lattice-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.image-lattice :as image]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (image/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest images-preserve-unions-and-injective-intersections
  (let [checked-environment @checked-environment
        theorems (image/theorem-ids checked-environment)]
    (is (= #{'set/image-union-subset-union-images
             'set/union-images-subset-image-union
             'set/image-union-equivalent-union-images
             'set/image-intersection-subset-intersection-images
             'set/intersection-images-subset-image-intersection-of-injective
             'set/image-intersection-equivalent-intersection-images-of-injective}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
