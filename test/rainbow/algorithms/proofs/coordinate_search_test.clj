(ns rainbow.algorithms.proofs.coordinate-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.coordinate-search :as ahof-o32]
            [rainbow.algorithms.proofs.coordinate-search :as iteration]
            [rainbow.algorithms.reference.coordinate-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o20-nesterov/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O20 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o32/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest coordinate-search-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'search/coordinate-update-first 'search/coordinate-update-second
             'search/coordinate-cycle 'search/coordinate-iterate}
           (set (keys definitions))))
    (is (= #{'search/coordinate-update-first-unfold
             'search/coordinate-update-second-unfold
             'search/coordinate-cycle-unfold
             'search/coordinate-iterate-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o32-coordinate-search-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o32/theorem-ids checked-environment)]
    (is (= #{'ahof-o32/first-coordinate-descends-to-zero
             'ahof-o32/second-coordinate-descends-to-zero
             'ahof-o32/coordinate-recurrence
             'ahof-o32/coordinate-search}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-coordinate-cycle-composes-coordinates-in-turn
  ;; rate 1, positive-part partial gradients, from [2 2]. The first coordinate
  ;; descends to 0, then the second coordinate of the updated state descends to
  ;; 0, reaching [0 0]. The second update reads the state left by the first.
  (let [g0 (fn [[x _y]] (max 0 x))
        g1 (fn [[_x y]] (max 0 y))]
    (is (= [0 2] (executable/update-first 1 g0 [2 2])))
    (is (= [0 0] (executable/cycle-once 1 g0 g1 [2 2])))
    (is (= [0 0] (executable/run 1 g0 g1 1 [2 2])))
    ;; Zero cycles return the initial state.
    (is (= [2 2] (executable/run 1 g0 g1 0 [2 2])))))
