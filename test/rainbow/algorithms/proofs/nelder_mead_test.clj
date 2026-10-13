(ns rainbow.algorithms.proofs.nelder-mead-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.math.linear.vector.equivalence :as veq]
            [rainbow.algorithms.proofs.nelder-mead :as nelder]
            [rainbow.algorithms.reference.nelder-mead :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          veq/extend-environment
          nelder/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest nelder-mead-reflect-is-native-axiom-free
  (let [env @checked-environment
        definitions (nelder/definition-ids env)
        theorems (nelder/theorem-ids env)]
    (is (= #{'nelder/reflect} (set (keys definitions))))
    (is (= #{'nelder/reflect-unfold 'nelder/reflect-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-nelder-mead-reflects-exactly
  ;; Reflect the worst [1,1] through centroid [2,2]: [3,3].
  (is (= [3 3] (executable/reflect [2 2] [1 1])))
  ;; A non-uniform reflection: centroid [3,2], worst [1,0] -> [5,4].
  (is (= [5 4] (executable/reflect [3 2] [1 0])))
  ;; Centroid of a two-vertex simplex.
  (is (= [2 2] (executable/centroid [[1 1] [3 3]])))
  ;; Expansion beyond the reflection.
  (is (= [4 4] (executable/expand [2 2] [3 3] 2))))
