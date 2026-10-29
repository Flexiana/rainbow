(ns rainbow.math.rational.signed.lp-minimization-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.rational.signed.lp-minimization-bridge :as bridge]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (bridge/extend-environment (:environment r)))))
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r)) (throw (ex-info "Elaboration failed" {:result r})))
    (:term r)))
(defn- check [label spec]
  (let [v (core! (:value spec)) t (core! (:type spec))
        r (kernel/check @env v t #{})
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-MINIMIZATION" label (pr-str result))
    result))
(defn- rejected! [label spec]
  (let [r (check label spec)]
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (:category r)))))
(def ^:private mixed
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [2 -1]
   :plan [0 1/2] :prices [0 1] :sense :minimize})

(deftest actual-negation-and-universal-original-cost-bound
  (doseq [i [{:matrix [[1]] :capacities [1] :margins [-1]
             :plan [1/2] :prices [1] :sense :minimize}
            mixed]]
    (doseq [[label spec] (bridge/minimization-specs i -1)]
      (let [r (check [(count (:margins i)) label] spec)]
        (is (= :checked (:status r)))
        (is (= #{} (:axioms r)))))))

(deftest altered-coefficients-cannot-hide-at-a-zero-submitted-plan-component
  ;; The submitted plan starts with zero; its objective would not expose the
  ;; altered first coefficient. An all-index/all-candidate relation must do so.
  (rejected! :first-coefficient (bridge/coefficient-negation-spec [-1 1] [2 -1]))
  (rejected! :last-coefficient (bridge/coefficient-negation-spec [-2 2] [2 -1])))

(deftest too-high-original-lower-bound-is-rejected
  ;; Feasible candidate [0 1] costs -1. A universal lower bound of 0 is false.
  (rejected! :too-high-lower-bound
             (:universal-original-lower-bound (bridge/minimization-specs mixed 0))))

(deftest malformed-table-and-wrong-sense-are-host-refusals
  (doseq [[actual original] [[[] []] [[1] [1 2]]]]
    (is (= :lp-minimization/table-shape
           (try (bridge/coefficient-negation-spec actual original) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
  (is (= :lp-minimization/wrong-sense
         (try (bridge/minimization-specs (assoc mixed :sense :maximize) -1) :unexpected-success
              (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e)))))))
