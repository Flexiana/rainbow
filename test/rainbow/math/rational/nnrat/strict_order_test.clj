(ns rainbow.math.rational.nnrat.strict-order-test
  "Gate for the nnrat strict-order port: less-than + intro/implies-at-most/irreflexive/
  asymmetric/transitive and the two <=/< mixing lemmas, kernel-checked and axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.strict-order :as nso]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (nso/extend-environment (:environment checkpoint)))))

(deftest nnrat-strict-order-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (nso/theorem-ids env)]
    (is (= #{'nnrat/less-than 'nnrat/less-than-intro 'nnrat/less-than-implies-at-most
             'nnrat/less-than-irreflexive 'nnrat/less-than-asymmetric 'nnrat/less-than-transitive
             'nnrat/less-than-of-at-most-of-less-than 'nnrat/less-than-of-less-than-of-at-most}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
