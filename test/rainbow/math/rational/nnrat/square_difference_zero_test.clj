(ns rainbow.math.rational.nnrat.square-difference-zero-test
  "Gate for the nnrat AM-GM discriminant: (P*P+N*N ~ P*N+N*P) -> P ~ N (ordered and full),
  axiom-free -- the hard core of the no-zero-divisors chain."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.square-difference-zero :as sdz]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (sdz/extend-environment (:environment checkpoint)))))

(deftest square-difference-zero-is-checked-and-axiom-free
  (let [env @checked-environment
        ids (sdz/theorem-ids env)]
    (is (= #{'nnrat/square-difference-zero-ordered 'nnrat/square-difference-zero}
           (set (keys ids))))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked
               (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))
            (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
