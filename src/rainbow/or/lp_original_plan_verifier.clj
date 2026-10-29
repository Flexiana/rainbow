(ns rainbow.or.lp-original-plan-verifier
  "Experimental value-only replay for ORIGINAL LP plans and their reports.
  No producer dependency: targets are rebuilt from the receiver's request.
  The checked environment, specification encoder and host/JVM remain trusted."
  (:require [rainbow.canonical :as canonical]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.or.lp-certificate :as lp]))

(def report-obligations
  [:primal-feasibility-equivalence :objective-correspondence
   :dual-feasibility :dual-nonnegative :dual-endpoint-bound
   :universal-original-bound :submitted-plan-feasible :achieved-value
   :reported-gap :gap-nonnegative :reported-order])
(def optimality-obligations (into report-obligations [:tight-endpoint :optimality]))
(def epsilon-obligations (into report-obligations [:gap-within-budget :epsilon-optimal]))
(def ^:private claims
  {:feasible-report {:obligations report-obligations :status :original-plan-report-verified
                     :schema :lp-original-plan/v1}
   :optimal-plan {:obligations optimality-obligations :status :original-plan-optimal
                  :schema :lp-original-plan/v1}
   :epsilon-plan {:obligations epsilon-obligations :status :original-plan-epsilon-verified
                  :schema :lp-original-plan/v1-epsilon}})
(defn- refuse! [category message] (throw (ex-info message {:error/category category})))
(defn- bounded? [x]
  (and (or (integer? x) (ratio? x))
       (<= -10000 (if (ratio? x) (numerator x) x) 10000)
       (<= 1 (if (ratio? x) (denominator x) 1) 10000)))
(defn- numeric-vector? [xs n]
  (and (vector? xs) (= n (count xs)) (every? bounded? xs)))
(defn- table? [table n m]
  (and (vector? table) (= m (count table)) (every? #(numeric-vector? % n) table)))

(defn- validate! [original actual report proofs options]
  (when-not (and (map? options) (every? #{:claim :reductions :epsilon} (keys options))
                 (contains? claims (get options :claim :feasible-report))
                 (if (= :epsilon-plan (:claim options))
                   (and (contains? options :epsilon) (bounded? (:epsilon options))
                        (not (neg? (:epsilon options))))
                   (not (contains? options :epsilon)))
                 (integer? (get options :reductions 1000000))
                 (<= 1 (get options :reductions 1000000) 1000000))
    (refuse! :lp-original-plan/options "Unknown claim/options, invalid epsilon or reduction budget"))
  (let [required (:obligations (get claims (get options :claim :feasible-report)))]
    (when-not (and (map? proofs) (= (set required) (set (keys proofs))))
      (refuse! :lp-original-plan/evidence-shape "Exact claim-specific proof coverage is required")))
  ;; Type/size checks precede both literal encoding and any proof processing.
  (when-not (and (map? original) (map? actual) (map? report)
                 (vector? (:margins original)) (vector? (:matrix original))
                 (vector? (get original :equalities [])))
    (refuse! :lp-original-plan/input-shape "Expected finite original/actual tables and a report"))
  (let [n (count (:margins original)) m (count (:matrix original))
        eqs (get original :equalities []) expanded (+ m (* 2 (count eqs)))]
    (when-not
     (and (<= n 32) (<= expanded 32)
          (contains? #{nil :maximize :minimize} (:sense original))
          (table? (:matrix original) n m) (numeric-vector? (:capacities original) m)
          (numeric-vector? (:margins original) n) (numeric-vector? (:plan original) n)
          (every? #(and (map? %) (numeric-vector? (:row %) n) (bounded? (:value %))) eqs)
          (table? (:matrix actual) n expanded) (numeric-vector? (:capacities actual) expanded)
          (numeric-vector? (:margins actual) n) (numeric-vector? (:prices actual) expanded)
          (= #{:achieved :bound :gap :direction} (set (keys report)))
          (every? bounded? ((juxt :achieved :bound :gap) report))
          (= (:direction report) (if (= :minimize (:sense original)) :lower :upper)))
      (refuse! :lp-original-plan/input-shape "Expected bounded exact LP data and oriented report"))))

(defn- project-request [original actual report]
  ;; Deliberately excludes original dual prices and actual[:plan]/:sense: none
  ;; of those are interpreted by this certificate. Nested metadata is excluded.
  {:original (assoc (select-keys original [:matrix :capacities :margins :plan])
                    :sense (if (= :minimize (:sense original)) :minimize :maximize)
                    :equalities (mapv #(select-keys % [:row :value]) (get original :equalities [])))
   :actual (select-keys actual [:matrix :capacities :margins :prices])
   :report report})
(defn- claim-request [original actual report options]
  (cond-> (project-request original actual report)
    (= :epsilon-plan (:claim options)) (assoc :epsilon (:epsilon options))))
(defn request-id
  "Identify a validated receiver request without checking any evidence.
  This is NOT a verification result or authentication of a certificate. Throws
  on invalid request/options; exactly the same projection is used by verify."
  ([original actual report] (request-id original actual report {}))
  ([original actual report options]
   (let [required (:obligations (get claims (get options :claim :feasible-report)))]
     (validate! original actual report (zipmap required (repeat nil)) options)
     (canonical/content-id (claim-request original actual report options)))))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- expected-types [{:keys [original actual report epsilon]} claim]
  ;; Receiver-owned mathematical model; never standardize again, call a proof
  ;; builder, extract a target from supplied evidence, or decide numeric truth.
  (let [z (f/const* 'signed/zero []) truth (f/const* 'proposition/truth [])
        literal #'lp/signed-literal
        mapping (fn [xs] (if (seq xs) (#'lp/nat-lookup lp/signed (mapv literal xs))
                            (f/lam [['ignored lp/nat]] z)))
        cols (#'lp/index-list (count (:margins original)))
        rows (#'lp/index-list (count (:capacities actual)))
        sum (fn [m indices] (poly 'signed/map-sum lp/nat m indices))
        dot (fn [a v] (sum (f/lam [['j lp/nat]]
                                 (app 'signed/multiply (f/app (mapping a) 'j) (f/app v 'j))) cols))
        constraints (fn [v]
                      (let [clause (fn [rel a b] (app rel (dot a v) (literal b)))
                            clauses (concat (map #(clause 'signed/at-most %1 %2)
                                                 (:matrix original) (:capacities original))
                                            (map #(clause 'signed/equivalent (:row %) (:value %))
                                                 (:equalities original)))]
                        (reduce #(app 'proposition/conjunction %2 %1) truth (reverse clauses))))
        zero-on (f/lam [['ignored lp/nat]] z)
        nonnegative (fn [v] (poly 'signed/all-at-most lp/nat zero-on v cols))
        feasible (fn [v] (app 'proposition/conjunction (constraints v) (nonnegative v)))
        M (if (seq (:matrix actual))
            (#'lp/nat-lookup (f/arrow lp/nat lp/signed) (mapv mapping (:matrix actual)))
            (f/lam [['ignored lp/nat]] (mapping [])))
        b (mapping (:capacities actual)) c (mapping (:margins actual)) y (mapping (:prices actual))
        activity (f/lam [['i lp/nat]]
                        (sum (f/lam [['j lp/nat]]
                                    (app 'signed/multiply (f/app (f/app M 'i) 'j)
                                         (f/app 'candidate 'j))) cols))
        dual (f/lam [['j lp/nat]]
                    (sum (f/lam [['i lp/nat]]
                                (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app y 'i))) rows))
        OP (feasible 'candidate)
        AP (app 'proposition/conjunction (poly 'signed/all-at-most lp/nat activity b rows)
                (nonnegative 'candidate))
        Q (sum (f/lam [['i lp/nat]] (app 'signed/multiply (f/app b 'i) (f/app y 'i))) rows)
        O (dot (:margins original) 'candidate) S (dot (:margins actual) 'candidate)
        x (mapping (:plan original)) PX (feasible x) X (dot (:margins original) x)
        [A B G] (mapv literal ((juxt :achieved :bound :gap) report))
        minimum? (= :minimize (:sense original))
        SE (literal (if minimum? (- (:bound report)) (:bound report)))
        cb [['candidate (f/arrow lp/nat lp/signed)]]
        fb (conj cb ['original-feasible OP])
        targets
        {:primal-feasibility-equivalence (f/forall cb (app 'proposition/equivalence OP AP))
         :objective-correspondence (f/forall cb (app 'signed/equivalent S (if minimum? (app 'signed/negate O) O)))
         :dual-feasibility (poly 'signed/all-at-most lp/nat c dual cols)
         :dual-nonnegative (poly 'signed/all-at-most lp/nat zero-on y rows)
         :dual-endpoint-bound (app 'signed/at-most Q SE)
         :universal-original-bound (f/forall fb (if minimum? (app 'signed/at-most B O) (app 'signed/at-most O B)))
         :submitted-plan-feasible PX
         :achieved-value (app 'signed/equivalent X A)
         :reported-gap (app 'signed/equivalent (if minimum? A B) (app 'signed/add (if minimum? B A) G))
         :gap-nonnegative (app 'signed/at-most z G)
         :reported-order (if minimum? (app 'signed/at-most B A) (app 'signed/at-most A B))}]
    (case claim
      :optimal-plan
      (assoc targets :tight-endpoint (app 'signed/equivalent A B)
             :optimality (app 'proposition/conjunction PX
                              (f/forall fb (if minimum? (app 'signed/at-most X O) (app 'signed/at-most O X)))))
      :epsilon-plan
      (let [E (literal epsilon)
            improvement (if minimum? (app 'signed/subtract X O) (app 'signed/subtract O X))]
        (assoc targets :gap-within-budget (app 'signed/at-most G E)
               :epsilon-optimal (app 'proposition/conjunction PX
                                    (f/forall fb (app 'signed/at-most improvement E)))))
      targets)))

(defn- core! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (refuse! :lp-original-plan/elaboration "Evidence or receiver target did not elaborate"))
    (:term r)))
(defn- replay-one [env reductions proof target]
  (let [v (core! env proof) t (core! env target)
        r (binding [kernel/*reduction-budget* reductions] (kernel/check env v t #{}))
        category (get-in r [:error :error/category])]
    (if (= :checked (:status r))
      (let [closures (map #(kernel/axioms env %) (into (term/constants v) (term/constants t)))]
        (if (and (every? set? closures) (every? empty? closures))
          {:status :checked :axioms #{} :proof/id (canonical/content-id v) :type/id (canonical/content-id t)}
          {:status :rejected :error/category :lp-original-plan/axiom-policy}))
      {:status (if (= :kernel/resource-limit category) :refused :rejected)
       :error/category (or category :lp-original-plan/unexpected-kernel-status)})))

(defn verify
  "Check a complete original-plan certificate in an already-checked environment.
  :claim :feasible-report (default) requires 11 values; :optimal-plan requires 13.
  :epsilon-plan requires its own 13 keys and an exact bounded nonnegative :epsilon.
  Epsilon is part of the verified request/audit identity and the returned result;
  even epsilon=0 never upgrades the status to exact optimality.
  Numeric zero gap NEVER upgrades a claim. Rejection does not prove suboptimality.
  Actual tables are already expanded/max-oriented, not standardized by this API.
  Only the request projection described in project-request is identified/verified;
  original dual-price interpretation and actual[:plan] are explicitly excluded.
  Limits: 32 columns/expanded rows, bounded exact scalars, <=1e6 reductions PER
  normalization. No proof-size limit/process isolation or executable/L6 claim."
  ([env original actual report proofs] (verify env original actual report proofs {}))
  ([env original actual report proofs options]
   (try
     (validate! original actual report proofs options)
     (let [claim (get options :claim :feasible-report)
           {:keys [obligations status schema]} (get claims claim)
           reductions (get options :reductions 1000000)
           request (claim-request original actual report options)
           required obligations
           targets (expected-types request claim)]
       (loop [pending required verdicts (array-map)]
         (if-let [obligation (first pending)]
           (let [r (replay-one env reductions (get proofs obligation) (get targets obligation))
                 verdicts (assoc verdicts obligation r)]
             (if (= :checked (:status r)) (recur (next pending) verdicts)
               {:status (:status r) :failed-obligation obligation :verdicts verdicts}))
           (let [result (cond-> {:status status :claim claim
                                 :scope :original-plan-and-expanded-bound-certificate
                                 :request/id (canonical/content-id request)
                                 :required-obligations required :verdicts verdicts}
                          (= :epsilon-plan claim) (assoc :epsilon (:epsilon options)))]
             (assoc result :audit/id (canonical/content-id (assoc result :schema schema)))))))
     (catch clojure.lang.ExceptionInfo e
       {:status :refused :error/category (or (:error/category (ex-data e)) :lp-original-plan/check-exception)})
     (catch IllegalArgumentException _
       {:status :refused :error/category :lp-original-plan/malformed-term}))))
