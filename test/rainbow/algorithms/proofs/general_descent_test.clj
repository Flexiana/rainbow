(ns rainbow.algorithms.proofs.general-descent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.general-descent :as ahof-o13]
            [rainbow.algorithms.proofs.general-descent :as iteration]
            [rainbow.algorithms.reference.general-descent :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o19-momentum/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O19 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o13/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest general-descent-skeleton-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/general-descent-step
             'optimization/general-descent-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/general-descent-step-unfold
             'optimization/general-descent-iterate-zero
             'optimization/general-descent-iterate-successor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o13-general-descent-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o13/theorem-ids checked-environment)]
    (is (= #{'ahof-o13/trajectory-values
             'ahof-o13/descent-recurrence
             'ahof-o13/general-descent}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-general-descent-instantiates-to-gradient-descent
  ;; direction = const 1, step = 1/2, update = point - rate*direction, from 1.
  ;; The skeleton composes the three plug-ins into the O17 trajectory.
  (let [direction (fn [_p] 1)
        step-size (fn [_p] 1/2)
        update (fn [point rate dir] (- point (* rate dir)))]
    (is (= 1/2 (executable/step direction step-size update 1)))
    (is (= [1 1/2 0 -1/2]
           (mapv #(executable/run direction step-size update % 1)
                 [0 1 2 3])))
    ;; A different update rule (ascent) reuses the same skeleton.
    (let [ascent (fn [point rate dir] (+ point (* rate dir)))]
      (is (= 3/2 (executable/step direction step-size ascent 1))))))
