(ns rainbow.algorithms.proofs.bisection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bisection :as ahof-o12]
            [rainbow.algorithms.proofs.bisection :as iteration]
            [rainbow.algorithms.reference.bisection :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d14-network-scoring/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D14 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o12/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bisection-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'search/bracket-midpoint 'search/bisection-narrow}
           (set (keys definitions))))
    (is (= #{'search/bracket-midpoint-unfold 'search/narrow-keeps-lower
             'search/narrow-keeps-upper}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o12-bisection-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o12/theorem-ids checked-environment)]
    (is (= #{'ahof-o12/first-midpoint-is-half
             'ahof-o12/narrows-to-lower-half
             'ahof-o12/second-midpoint-is-quarter
             'ahof-o12/bisection}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bisection-halves-the-bracket-exactly
  ;; Probe of [0, 1] is the midpoint 1/2; keep-lower narrows to [0, 1/2];
  ;; the next probe 1/4 -- interval and probe both halve.
  (is (= 1/2 (executable/midpoint 0 1)))
  (is (= [0 1/2] (executable/narrow true 0 1)))
  (is (= [1/2 1] (executable/narrow false 0 1)))
  (is (= 1/4 (executable/midpoint 0 1/2)))
  ;; Narrowing exactly halves the bracket width.
  (is (= (/ (executable/width [0 1]) 2)
         (executable/width (executable/narrow true 0 1)))))
