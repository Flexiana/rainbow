(ns rainbow.or.lp-model-test
  "The derivation must reproduce a hand-written instance EXACTLY, or it is not a
  substitute for one -- it is a second thing to keep in sync."
  (:require [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-model :as model]))

;; the order-acceptance instance from lp_certificate_test, stated as the
;; business facts it came from rather than as a grid
(def order-acceptance-description
  {:activities [{:name "order-A" :margin 8}
                {:name "order-B" :margin 6}
                {:name "rush-job" :margin 9}
                {:name "setup"    :margin -2}]
   :resources [{:name "machine-hours" :capacity 10
                :consumption {"order-A" 4 "order-B" 5}}
               {:name "finishing-hours" :capacity 8
                :consumption {"rush-job" 6}}
               {:name "order-A-limit" :capacity 1 :consumption {"order-A" 1}}
               {:name "order-B-limit" :capacity 1 :consumption {"order-B" 1}}
               {:name "rush-job-limit" :capacity 1 :consumption {"rush-job" 1}}
               {:name "rush-needs-setup" :capacity 0
                :consumption {"rush-job" 1 "setup" -1}}
               {:name "setup-limit" :capacity 1 :consumption {"setup" 1}}]
   :plan {"order-A" 1 "order-B" 1 "rush-job" 1 "setup" 1}
   :prices {"rush-job-limit" 8 "order-A-limit" 6 "order-B-limit" 9}})

(deftest the-derivation-reproduces-the-hand-written-instance
  (testing "matrix, capacities and margins come out exactly as written by hand"
    (let [derived (model/derive-instance order-acceptance-description)]
      (is (= [[4 5 0 0] [0 0 6 0] [1 0 0 0] [0 1 0 0]
              [0 0 1 0] [0 0 1 -1] [0 0 0 1]]
             (:matrix derived)))
      (is (= [10 8 1 1 1 0 1] (:capacities derived)))
      (is (= [8 6 9 -2] (:margins derived)))
      (is (= [1 1 1 1] (:plan derived)))))
  (testing "undeclared consumption is zero, and that is stated not stumbled into"
    ;; 'setup' consumes nothing from machine-hours, so column 4 of row 0 is 0
    (is (= 0 (get-in (model/derive-instance order-acceptance-description)
                     [:matrix 0 3])))))

(deftest every-coefficient-traces-back-to-a-named-fact
  (testing "the explanation names each activity's worth and each resource's use"
    (let [lines (model/explain order-acceptance-description)]
      (is (= 11 (count lines)) "four activities and seven resources")
      (is (some #(string/includes? % "activity 'order-A' is worth 8") lines))
      (is (some #(and (string/includes? % "resource 'machine-hours'")
                      (string/includes? % "capacity 10")
                      (string/includes? % "order-A x4")) lines))
      ;; the batch-linking row is the one a reader most needs rendered in words
      (is (some #(and (string/includes? % "rush-needs-setup")
                      (string/includes? % "setup x-1")) lines)))))

(deftest typos-that-would-vanish-into-a-zero-column-are-caught
  (testing "consumption naming an activity that does not exist"
    (let [faults (model/check-description
                  (update-in order-acceptance-description [:resources 0 :consumption]
                             assoc "order-C" 3))]
      (is (= [:consumption-names-unknown-activity] (mapv :fault faults)))
      (is (= [{:resource "machine-hours" :unknown-activity "order-C"}]
             (:detail (first faults))))))
  (testing "a plan naming an activity that does not exist"
    (let [faults (model/check-description
                  (assoc-in order-acceptance-description [:plan "order-Z"] 1))]
      (is (= [:plan-names-unknown-activity] (mapv :fault faults)))))
  (testing "a well-formed description has no faults"
    (is (= [] (model/check-description order-acceptance-description)))))

;; ---- the description reaching the kernel ------------------------------------

(def base
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lp-on/extend-environment
          decide-order/extend-environment))))

(deftest a-description-is-certified-and-carries-its-own-explanation
  (testing "business facts in, kernel-checked bound out"
    (let [result (model/bound-described
                  @base
                  (assoc order-acceptance-description
                         ;; read off the source instance, not retyped from
                         ;; memory: prices [0 0 8 6 9 0 0] over resources in
                         ;; declared order maps order-A-limit 8, order-B-limit
                         ;; 6, rush-job-limit 9
                         :prices {"machine-hours" 0 "finishing-hours" 0
                                  "order-A-limit" 8 "order-B-limit" 6
                                  "rush-job-limit" 9 "rush-needs-setup" 0
                                  "setup-limit" 0})
                  {:alias 'optimization/described-bound})]
      (is (= :bounded (:status result)))
      ;; the audit trail carries the facts, not just the numbers
      (is (= (:activities order-acceptance-description)
             (:activities (:description result))))
      (is (= (:resources order-acceptance-description)
             (:resources (:description result))))
      (is (some #(re-find #"machine-hours" %) (:explanation result)))
      (is (contains? result :audit/id)))))

(deftest a-malformed-description-is-refused-before-any-kernel-work
  (testing "a misspelled activity is a refusal, not a silent zero column"
    (let [result (model/bound-described
                  @base
                  (update-in order-acceptance-description [:resources 0 :consumption]
                             assoc "order-C" 3)
                  {:alias 'optimization/malformed-described})]
      (is (= :rejected (:status result)))
      (is (= :lp-model/malformed-description (:error/category result)))
      (is (= [:consumption-names-unknown-activity] (mapv :fault (:faults result)))))))
