(ns rainbow.or.lp-original-plan-verifier-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-plan-report-bridge :as producer]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.or.lp-original-plan-verifier :as verifier]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (producer/extend-environment (:environment r)))))
(def ^:private maximum {:matrix [[1]] :capacities [2] :margins [1] :prices [1] :plan [2]})
(def ^:private minimum {:matrix [[-1]] :capacities [-1] :margins [1] :prices [1] :plan [1] :sense :minimize})
(def ^:private equality {:matrix [] :capacities [] :margins [1 1] :prices [] :plan [1 0]
                        :equalities [{:row [1 1] :value 1}] :equality-prices [1]})
(def ^:private report {:achieved 2 :bound 2 :gap 0 :direction :upper})
(defn- proofs [original actual r optimal?]
  (into {} (map (fn [[k v]] [k (:value v)]))
        ((if optimal? producer/optimality-specs producer/plan-report-specs) original actual r)))
(def ^:private actual (#'lp/standard-form maximum))
(def ^:private optimal-proofs (delay (proofs maximum actual report true)))
(defn- show [label r]
  (println "LP-ORIGINAL-PLAN-VERIFIER" label
           (pr-str (select-keys r [:status :claim :failed-obligation :error/category :request/id :audit/id])))
  r)
(defn- accepted! [r status n]
  (is (= status (:status r)))
  (is (= n (count (:verdicts r))))
  (is (every? #(and (= :checked (:status %)) (= #{} (:axioms %))) (vals (:verdicts r))))
  (is (string? (:audit/id r))))

(deftest real-proofs-independent-receiver-both-senses-equalities-and-empty
  (doseq [[label original r]
          [[:maximum maximum report]
           [:minimum minimum {:achieved 1 :bound 1 :gap 0 :direction :lower}]
           [:equality equality {:achieved 1 :bound 1 :gap 0 :direction :upper}]
           [:empty {:matrix [] :capacities [] :margins [] :plan [] :prices []}
            {:achieved 0 :bound 0 :gap 0 :direction :upper}]]]
    (let [a (#'lp/standard-form original) p (proofs original a r true) e @env
          result (with-redefs [producer/plan-report-specs (fn [& _] (throw (AssertionError. "Producer called")))
                              producer/optimality-specs (fn [& _] (throw (AssertionError. "Producer called")))]
                   (verifier/verify e original a r p {:claim :optimal-plan}))]
      (accepted! (show label result) :original-plan-optimal 13))))

(deftest report-status-does-not-silently-upgrade-to-optimal
  (let [p (select-keys @optimal-proofs verifier/report-obligations)]
    (accepted! (show :zero-gap-basic (verifier/verify @env maximum actual report p))
               :original-plan-report-verified 11)
    (is (= :refused (:status (verifier/verify @env maximum actual report p {:claim :optimal-plan})))))
  (doseq [[original r] [[(assoc maximum :plan [1]) {:achieved 1 :bound 2 :gap 1 :direction :upper}]
                        [(assoc minimum :plan [2]) {:achieved 2 :bound 1 :gap 1 :direction :lower}]]]
    (let [a (#'lp/standard-form original)]
      (accepted! (show :positive-gap (verifier/verify @env original a r (proofs original a r false)))
                 :original-plan-report-verified 11)
      (let [result (show :not-tight (verifier/verify @env original a r (proofs original a r true)
                                                    {:claim :optimal-plan}))]
        (is (= :rejected (:status result)))
        (is (= :tight-endpoint (:failed-obligation result)))))))

(deftest every-obligation-is-required-and-every-slot-is-actually-checked
  (let [e @env p @optimal-proofs]
    (doseq [k verifier/optimality-obligations]
      (let [missing (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Shape must fail first")))]
                      (verifier/verify nil maximum actual report (dissoc p k) {:claim :optimal-plan}))
            altered (show [:replace k]
                          (verifier/verify e maximum actual report (assoc p k (f/const* 'proposition/trivial []))
                                           {:claim :optimal-plan}))]
        (is (= :lp-original-plan/evidence-shape (:error/category missing)))
        (is (= :rejected (:status altered)))
        (is (= k (:failed-obligation altered)))
        (is (= :kernel/type-mismatch (get-in altered [:verdicts k :error/category])))))
    (doseq [bad [(assoc p :extra (:optimality p)) {}]]
      (is (= :lp-original-plan/evidence-shape
             (:error/category (verifier/verify nil maximum actual report bad {:claim :optimal-plan})))))))

(deftest request-tampering-and-fake-zero-gap-do-not-certify
  (doseq [[label original a r expected]
          [[:plan (assoc maximum :plan [1]) actual report :submitted-plan-feasible]
           [:original-constraint (assoc maximum :capacities [3]) actual report :primal-feasibility-equivalence]
           [:actual-constraint maximum (assoc actual :capacities [3]) report :primal-feasibility-equivalence]
           [:objective (assoc maximum :margins [2]) actual report :objective-correspondence]
           [:achieved maximum actual (assoc report :achieved 1) :achieved-value]
           [:gap maximum actual (assoc report :gap -1) :reported-gap]]]
    (let [r (show label (verifier/verify @env original a r @optimal-proofs {:claim :optimal-plan}))]
      (is (= :rejected (:status r))) (is (= expected (:failed-obligation r)))))
  (let [original (assoc maximum :plan [1]) a (#'lp/standard-form original)
        r {:achieved 1 :bound 2 :gap 0 :direction :upper}
        result (show :forged-zero-gap (verifier/verify @env original a r (proofs original a r true)
                                                      {:claim :optimal-plan}))]
    (is (= :rejected (:status result))) (is (= :reported-gap (:failed-obligation result))))
  (let [original (assoc equality :plan [2 -1]) a (#'lp/standard-form original)
        r {:achieved 1 :bound 1 :gap 0 :direction :upper}
        result (show :infeasible-zero-gap (verifier/verify @env original a r (proofs original a r true)
                                                          {:claim :optimal-plan}))]
    (is (= :rejected (:status result))) (is (= :submitted-plan-feasible (:failed-obligation result)))))

(deftest identity-covers-only-the-verified-projection-and-includes-claim
  (let [p @optimal-proofs e @env
        r1 (verifier/verify e maximum actual report p {:claim :optimal-plan})
        r2 (verifier/verify e (assoc maximum :prices [999] :private-note "not certified")
                            (assoc actual :plan [-999] :sense :minimize) report p {:claim :optimal-plan})
        basic (verifier/verify e maximum actual report (select-keys p verifier/report-obligations))]
    (accepted! r2 :original-plan-optimal 13)
    (is (= (:request/id r1) (:request/id r2) (:request/id basic)))
    (is (= (:audit/id r1) (:audit/id r2)))
    (is (not= (:audit/id r1) (:audit/id basic)))))

(deftest malformed-inputs-and-options-refused-before-encoding
  (let [p @optimal-proofs]
    (doseq [[o a r opts]
            [[maximum actual (assoc report :status :optimal) {:claim :optimal-plan}]
             [maximum actual (assoc report :gap 0.0) {:claim :optimal-plan}]
             [maximum actual (assoc report :direction :lower) {:claim :optimal-plan}]
             [(assoc maximum :plan [18446744073709551616N]) actual report {:claim :optimal-plan}]
             [(assoc maximum :equalities nil) actual report {:claim :optimal-plan}]
             [maximum (assoc actual :prices []) report {:claim :optimal-plan}]
             [maximum (assoc actual :margins [1/10001]) report {:claim :optimal-plan}]
             [maximum actual report {:claim :unknown}]
             [maximum actual report {:claim :optimal-plan :reductions 0}]
             [maximum actual report {:claim :optimal-plan :reductions 1000001}]
             [maximum actual report {:claim :optimal-plan :skip [:optimality]}]]]
      (let [r (with-redefs-fn {#'lp/signed-literal (fn [& _] (throw (AssertionError. "Encoder reached")))
                              #'kernel/check (fn [& _] (throw (AssertionError. "Kernel reached")))}
                #(verifier/verify nil o a r p opts))]
        (is (= :refused (:status r)))))))

(deftest replay-failures-and-unknown-axioms-fail-closed
  ;; Injected boundary responses test policy only, not mathematical validity.
  (let [e @env p @optimal-proofs]
    (doseq [[response status] [[{:status :rejected :error {:error/category :kernel/resource-limit}} :refused]
                               [{:status :unexpected} :rejected]]]
      (let [r (with-redefs [kernel/check (fn [& _] response)]
                (verifier/verify e maximum actual report p {:claim :optimal-plan}))]
        (is (= status (:status r))) (is (= :primal-feasibility-equivalence (:failed-obligation r)))))
    (doseq [closure [nil #{'test/unsupported-axiom}]]
      (let [r (with-redefs [kernel/axioms (fn [& _] closure)]
                (verifier/verify e maximum actual report p {:claim :optimal-plan}))]
        (is (= :rejected (:status r)))
        (is (= :lp-original-plan/axiom-policy
               (get-in r [:verdicts :primal-feasibility-equivalence :error/category])))))
    (let [r (verifier/verify e maximum actual report
                             (assoc p :primal-feasibility-equivalence
                                    {:value (f/const* 'proposition/trivial []) :type (f/const* 'proposition/truth [])})
                             {:claim :optimal-plan})]
      (is (= :refused (:status r)))
      (is (= :lp-original-plan/elaboration (:error/category r))))))
