(ns rainbow.math.rational.signed.lp-report-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.rational.signed.lp-report-bridge :as report]))

(def ^:private env
  (delay
    (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
      (report/extend-environment (:environment r)))))

(defn- elaborate! [e expression]
  (let [r (elaborate/core-expression e expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Report proof did not elaborate" {:result r})))
    (:term r)))

(defn- check [spec]
  (let [e @env v (elaborate! e (:value spec)) t (elaborate! e (:type spec))
        r (binding [kernel/*reduction-budget* 500000] (kernel/check e v t #{}))
        result (assoc {:status (:status r)
                       :error (select-keys (:error r) [:error/category :operation])} :axioms
                      (when (= :checked (:status r))
                        (into #{} (mapcat #(kernel/axioms e %) (term/constants v)))))]
    (println "LP-REPORT-CHECK" (pr-str result))
    result))

(def ^:private instance
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [1 1]
   :plan [1/2 1/2] :prices [1 1]})
(def ^:private valid {:achieved 1 :bound 2 :gap 1 :direction :upper})

(deftest original-report-fields-are-bound-to-the-formal-sums
  (doseq [[_ spec] (:specs (report/report-specs instance valid))]
    (let [r (check spec)]
      (is (= :checked (:status r)) (pr-str r))
      (is (= #{} (:axioms r))))))

(deftest changed-report-fields-are-type-rejected
  ;; These altered numbers can still satisfy a <= b. The correspondence
  ;; obligations, not a fresh literal comparison, must reject each alteration.
  (doseq [field [:achieved :bound :gap]]
    (let [spec (get-in (report/report-specs instance (update valid field inc)) [:specs field])
          r (check spec)]
      (is (= :rejected (:status r)) (pr-str r))
      (is (= :kernel/type-mismatch (get-in r [:error :error/category])) (pr-str r)))))

(deftest minimization-report-uses-negated-standard-form-order
  (let [i {:matrix [[1]] :capacities [1] :margins [-1]
           :plan [1/2] :prices [1] :sense :minimize}
        r (report/report-specs i {:achieved -1/2 :bound -1 :gap 1/2 :direction :lower})]
    (is (= :negated-minimization (:orientation r)))
    (doseq [[_ spec] (:specs r)]
      (let [verdict (check spec)]
        (is (= :checked (:status verdict)) (pr-str verdict))
        (is (= #{} (:axioms verdict)))))))

(deftest malformed-report-fields-are-host-refused-not-proof-rejections
  (doseq [r [(dissoc valid :bound) (assoc valid :gap 1.0)
             (assoc valid :direction :lower) (assoc valid :achieved "1")]]
    (is (= :lp-report/invalid-report
           (try (report/report-specs instance r) :unexpected-success
                (catch clojure.lang.ExceptionInfo e (:error/category (ex-data e))))))))
