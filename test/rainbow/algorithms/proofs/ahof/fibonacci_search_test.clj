(ns rainbow.algorithms.proofs.ahof.fibonacci-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.fibonacci-search :as specialization]
            [rainbow.algorithms.proofs.golden-section-search :as iteration]
            [rainbow.algorithms.reference.golden-section-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          specialization/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

;; O8 reuses the shared linesearch/* lemma; here we check the O8-specific
;; specialization declarations are native and axiom-free.
(deftest fibonacci-search-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'ahof-o8/left-value 'ahof-o8/right-value
             'ahof-o8/keeps-left 'ahof-o8/retains-min-left
             'ahof-o8/keeps-right-when-swapped 'ahof-o8/retains-min-right
             'ahof-o8/fibonacci-search}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-fibonacci-search-matches-worked-instance
  (is (true? (executable/keep-left? 3/8 5/8)))
  (is (= 3/8 (executable/retained-min 3/8 5/8)))
  (is (false? (executable/keep-left? 5/8 3/8)))
  (is (= 3/8 (executable/retained-min 5/8 3/8))))
