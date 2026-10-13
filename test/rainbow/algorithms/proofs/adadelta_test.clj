(ns rainbow.algorithms.proofs.adadelta-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.adadelta :as adadelta]
            [rainbow.algorithms.reference.adadelta :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (adadelta/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest adadelta-scale-is-native-axiom-free
  (let [env @checked-environment
        definitions (adadelta/definition-ids env)
        theorems (adadelta/theorem-ids env)]
    (is (= #{'adadelta/square-root? 'adadelta/scale} (set (keys definitions))))
    (is (= #{'adadelta/three-is-root-of-nine 'adadelta/scale-example
             'adadelta/scale-above-one-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-adadelta-scales-without-a-learning-rate
  ;; Update accumulator 4 (root 2) over gradient accumulator 9 (root 3): 2/3.
  (is (= 2/3 (executable/scale 4 9)))
  ;; A larger recent update than gradient: 9 over 4 gives 3/2.
  (is (= 3/2 (executable/scale 9 4)))
  ;; Equal statistics give a unit scale.
  (is (= 1 (executable/scale 4 4))))
