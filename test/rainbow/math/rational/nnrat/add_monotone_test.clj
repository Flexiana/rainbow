(ns rainbow.math.rational.nnrat.add-monotone-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.add-monotone :as am]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (-> (:environment c)
          am/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest nnrat-add-right-monotone-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (am/definition-ids env) (am/theorem-ids env))]
    (is (= #{'nnrat/add-right-monotone-base 'nnrat/add-right-monotone
             'nnrat/add-commutative 'nnrat/add-left-monotone 'nnrat/add-monotone}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
