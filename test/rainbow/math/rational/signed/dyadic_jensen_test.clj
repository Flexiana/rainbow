(ns rainbow.math.rational.signed.dyadic-jensen-test
  "Gate for dyadic (four-point) Jensen: 1/2+1/2~1 and the four-point convexity inequality,
  kernel-checked and axiom-free. f is abstract, so the type stays cheap to check."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.dyadic-jensen :as jensen]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (jensen/extend-environment (:environment checkpoint)))))

(deftest dyadic-jensen-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (jensen/theorem-ids env)]
    (is (= #{'nnrat/half-add-self-equivalent-one 'signed/dyadic-jensen-four}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
