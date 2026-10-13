(ns rainbow.algorithms.proofs.ahof.golden-section-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.golden-section-search :as specialization]
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

(deftest golden-section-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (iteration/definition-ids env) (iteration/theorem-ids env)
                   (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'linesearch/keep-left? 'linesearch/retained-min
             'linesearch/keep-left-unfold 'linesearch/retained-min-unfold
             'ahof-o9/left-value 'ahof-o9/right-value
             'ahof-o9/keeps-left 'ahof-o9/retains-min-left
             'ahof-o9/keeps-right-when-swapped 'ahof-o9/retains-min-right
             'ahof-o9/golden-section}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-golden-section-matches-worked-instance
  (is (true? (executable/keep-left? 1/2 3/4)))
  (is (= 1/2 (executable/retained-min 1/2 3/4)))
  (is (false? (executable/keep-left? 3/4 1/2)))
  (is (= 1/2 (executable/retained-min 3/4 1/2))))
