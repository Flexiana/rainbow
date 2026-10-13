(ns rainbow.math.finite.markov-dobrushin-statement-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.finite.markov-dobrushin-statement :as statement]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (statement/extend-environment (:environment checkpoint)))))

(deftest contraction-is-a-checked-proposition-not-a-proved-theorem
  (let [env @checked-environment
        id (get (statement/definition-ids env) 'markov/nnrat-dobrushin-contraction-estimate)
        d (environment/declaration env id)
        claimed-proof-type
        (f/forall statement/parameters
          (f/app (f/const* 'markov/nnrat-dobrushin-contraction-estimate [statement/U])
                 'S 'states 'kernel 'rho))
        result (elaborate/core-expression env claimed-proof-type)]
    (is (some? id))
    (is (= :definition (:rainbow/kind d)))
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
    (is (= #{} (kernel/axioms env id)))
    (is (empty? (statement/theorem-ids env)))
    (is (= :elaborated (:status result)))
    ;; The definition constructs a proposition; it cannot serve as its proof.
    (is (= :rejected (:status (kernel/check env (:rainbow/value d) (:term result) #{'u}))))))
