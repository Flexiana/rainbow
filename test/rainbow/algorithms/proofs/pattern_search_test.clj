(ns rainbow.algorithms.proofs.pattern-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pattern-search :as ahof-o35]
            [rainbow.algorithms.proofs.pattern-search :as iteration]
            [rainbow.algorithms.reference.pattern-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o16-trust-region/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O16 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o35/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest pattern-search-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'search/poll-better 'search/poll-improves 'search/pattern-move}
           (set (keys definitions))))
    (is (= #{'search/poll-better-unfold 'search/poll-improves-unfold
             'search/pattern-move-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o35-pattern-search-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o35/theorem-ids checked-environment)]
    (is (= #{'ahof-o35/poll-picks-backward
             'ahof-o35/move-accepts-best
             'ahof-o35/pattern-search}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-pattern-search-polls-the-better-candidate
  ;; Minimize x^2 from x=2 with step 1: poll x+1=3 (objective 9) and x-1=1
  ;; (objective 1). The poll picks 1 (smaller objective), which improves on the
  ;; current objective f(2)=4, so the step moves to 1 -- using only comparisons.
  (let [f (fn [x] (* x x))]
    (is (= 1 (executable/poll-better (f 3) (f 1) 3 1)))
    (is (= 3 (executable/poll-better (f 1) (f 3) 3 1)))
    (is (true? (executable/poll-improves? 1 4)))
    (is (= 1 (executable/step f 2 3 1)))
    ;; When neither candidate improves, the step keeps the current point.
    (is (= 2 (executable/step f 2 5 4)))))
