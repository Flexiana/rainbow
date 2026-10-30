(ns rainbow.or.lp-report-verifier
  "Independent replay boundary for LP numeric-report proofs.
  Supplied evidence contains proof VALUES only; expected types are reconstructed
  from the caller's instance/report, never taken from the proof producer.
  This verifies four report relations, not the LP executable or universal bound."
  (:require [rainbow.canonical :as canonical]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as f]
            [rainbow.or.lp-certificate :as lp]))

(def required-obligations [:achieved :bound :gap :numeric-order])
(def ^:private report-fields [:achieved :bound :gap :direction])
(def ^:private instance-fields
  [:matrix :capacities :margins :plan :prices :sense :equalities :equality-prices])
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- refuse! [category message]
  (throw (ex-info message {:error/category category})))

(defn- bounded-exact? [x]
  ;; The existing unary encoder casts to long. Reject oversized exact values
  ;; BEFORE that cast; a huge integer must not alias a different literal.
  (and (or (integer? x) (ratio? x))
       (let [n (if (ratio? x) (numerator x) x)
             d (if (ratio? x) (denominator x) 1)]
         (and (<= -10000 n 10000) (<= 1 d 10000)))))
(defn- numeric-vector? [xs n]
  (and (vector? xs) (= n (count xs)) (every? bounded-exact? xs)))

(defn- validate-budget! [reductions]
  (when-not (and (integer? reductions) (<= 1 reductions 1000000))
    (refuse! :lp-report/reduction-budget "Reduction budget must be between 1 and 1000000")))

(defn- bounded-lp-data?
  "Bounded exact rectangular LP data: at most 32 columns and expanded rows."
  [{:keys [matrix capacities margins plan prices equalities equality-prices]}]
  (let [n (when (vector? margins) (count margins))
        m (when (vector? capacities) (count capacities))
        eqs (or equalities []) ep (or equality-prices [])]
    (and n m (<= 1 n 32) (<= m 32)
         (vector? eqs) (<= 1 (+ m (* 2 (count eqs))) 32)
         (vector? matrix) (= m (count matrix))
         (every? #(numeric-vector? % n) matrix)
         (numeric-vector? capacities m) (numeric-vector? prices m)
         (numeric-vector? margins n) (numeric-vector? plan n)
         (numeric-vector? ep (count eqs))
         (every? #(and (map? %) (numeric-vector? (:row %) n)
                       (bounded-exact? (:value %))) eqs))))

(defn- fail-closed
  "Runs `check`, reporting a refusal or a malformed term as :refused."
  [check]
  (try
    (check)
    (catch clojure.lang.ExceptionInfo e
      {:status :refused :error/category (or (:error/category (ex-data e))
                                            :lp-report/check-exception)})
    (catch IllegalArgumentException _
      {:status :refused :error/category :lp-report/malformed-term})))

(defn- validate! [instance report proofs reductions]
  (when-not (and (map? instance) (map? report) (map? proofs)
                 (= (set required-obligations) (set (keys proofs))))
    (refuse! :lp-report/evidence-shape "Exactly four named proof values are required"))
  (validate-budget! reductions)
  (let [sense (:sense instance)]
    (when-not
     (and (bounded-lp-data? instance)
          (contains? #{nil :maximize :minimize} sense)
          (every? bounded-exact? (map report [:achieved :bound :gap]))
          (= (:direction report) (if (= :minimize sense) :lower :upper)))
      (refuse! :lp-report/input-shape
               "Expected bounded exact rectangular LP data and report direction"))))

(defn- expected-types [instance report]
  ;; Specification construction is part of the replay boundary. This deliberately
  ;; does NOT call report-specs or accept the producer's claimed target types.
  (let [standard (#'lp/standard-form instance)
        {:keys [x objective dual-objective]} (#'lp/instance-terms standard)
        primal (objective x) dual dual-objective
        orient (if (= :minimize (:sense instance)) - identity)
        a (#'lp/signed-literal (orient (:achieved report)))
        b (#'lp/signed-literal (orient (:bound report)))
        g (#'lp/signed-literal (:gap report))]
    {:achieved (app 'signed/equivalent primal a)
     :bound (app 'signed/equivalent dual b)
     :gap (app 'signed/equivalent dual (app 'signed/add primal g))
     :numeric-order (app 'signed/at-most a b)}))

(defn- core! [env surface]
  (let [r (elaborate/core-expression env surface)]
    (when-not (= :elaborated (:status r))
      (refuse! :lp-report/elaboration "Proof value or expected type did not elaborate"))
    (:term r)))

(defn- replay-one [env reductions proof expected]
  (let [v (core! env proof) t (core! env expected)
        r (binding [kernel/*reduction-budget* reductions] (kernel/check env v t #{}))
        category (get-in r [:error :error/category])]
    (if (= :checked (:status r))
      (let [closures (map #(kernel/axioms env %)
                          (into (term/constants v) (term/constants t)))]
        (if (and (every? set? closures) (every? empty? closures))
          {:status :checked :axioms #{}
           :proof-id (canonical/content-id v) :type-id (canonical/content-id t)}
          {:status :rejected :error/category :lp-report/axiom-policy}))
      {:status (if (= :kernel/resource-limit category) :refused :rejected)
       :error/category (or category :lp-report/unexpected-kernel-status)})))

(defn- replay-all
  "Replays `obligations` in order and stops at the first that does not check."
  [env reductions proofs types obligations verified]
  (loop [pending obligations verdicts (array-map)]
    (if-let [obligation (first pending)]
      (let [r (replay-one env reductions (get proofs obligation) (get types obligation))
            verdicts (assoc verdicts obligation r)]
        (if (= :checked (:status r))
          (recur (next pending) verdicts)
          {:status (:status r) :failed-obligation obligation :verdicts verdicts}))
      (verified verdicts))))

;; ---------------------------------------------------------------------------
;; Nine-obligation witnessed verification. The four report relations above only
;; show the SUBMITTED numbers agree with the standard-form objective/dual; they say
;; nothing about feasibility, dual feasibility or a bound against EVERY candidate.
;; The five structural witnesses close that gap (see verify-witnessed-report).
(def witness-obligations
  [:primal-feasibility :primal-nonnegative :dual-feasibility :dual-nonnegative
   :universal-reported-bound])
(def all-obligations (into required-obligations witness-obligations))

(defn- all-at-most [left right indices]
  (f/app (f/const* 'signed/all-at-most [[:zero]]) lp/nat left right indices))

(defn- expected-witness-types [instance reported-bound]
  ;; Reconstructed independently via the same standard-form interpretation the
  ;; report relations use. Never consults the producer's claimed witness types.
  (let [standard (#'lp/standard-form instance)
        {:keys [b c x y rows cols row-activity dual-price zero-on objective]}
        (#'lp/instance-terms standard)
        bound (#'lp/signed-literal (if (= :minimize (:sense instance))
                                     (- reported-bound) reported-bound))]
    {:primal-feasibility (all-at-most (row-activity x) b rows)
     :primal-nonnegative (all-at-most (zero-on) x cols)
     :dual-feasibility   (all-at-most c dual-price cols)
     :dual-nonnegative   (all-at-most (zero-on) y rows)
     :universal-reported-bound
     (f/forall [['candidate (f/arrow lp/nat lp/signed)]
                ['feasible (all-at-most (row-activity 'candidate) b rows)]
                ['nonnegative (all-at-most (zero-on) 'candidate cols)]]
               (app 'signed/at-most (objective 'candidate) bound))}))

(defn- validate-witnessed! [instance report proofs reductions reported-bound]
  ;; Reuse the four-obligation instance/report/budget shape checks, then add the
  ;; nine-key coverage requirement and the reported-bound scalar guard.
  (validate! instance report (select-keys proofs required-obligations) reductions)
  (when-not (= (set all-obligations) (set (keys proofs)))
    (refuse! :lp-report/evidence-shape "Exactly nine named proof values are required"))
  (when-not (bounded-exact? reported-bound)
    (refuse! :lp-report/input-shape "Reported bound must be a bounded exact scalar")))

(defn verify-witnessed-report
  "Replay all NINE proof values -- the four report relations plus the five
  structural witnesses (primal/dual feasibility, primal/dual nonnegativity, and
  the universal reported bound) -- in a supplied already-checked environment.

  Every expected type is reconstructed from the caller's instance/report and the
  explicit `reported-bound` scalar; producer-claimed types are never used. The
  universal bound is quantified over EVERY candidate satisfying the listed row
  constraints and column nonnegativity, so a plan-specific proof cannot pass it,
  and an infeasible plan fails its own feasibility obligation. Returns
  :report-verified only when all nine check axiom-free; any unmet obligation
  fails the whole bundle (fail-closed). Same limits as verify-report; the
  standard-form interpretation and literal encoding remain trusted."
  ([env instance report reported-bound proofs]
   (verify-witnessed-report env instance report reported-bound proofs {}))
  ([env instance report reported-bound proofs {:keys [reductions] :or {reductions 500000}}]
   (fail-closed
    (fn []
      (validate-witnessed! instance report proofs reductions reported-bound)
      (let [instance (select-keys instance instance-fields)
            report (select-keys report report-fields)
            types (merge (expected-types instance report)
                         (expected-witness-types instance reported-bound))]
        (replay-all
         env reductions proofs types all-obligations
         (fn [verdicts]
           {:status :report-verified
            :scope :original-standard-form-report-and-witnesses
            :required-obligations all-obligations :verdicts verdicts
            :orientation (if (= :minimize (:sense instance)) :negated-minimization :maximization)
            :reported-bound reported-bound
            :audit/id (canonical/content-id {:schema :lp-report/v2-witnessed
                                             :instance instance :report report
                                             :reported-bound reported-bound
                                             :verdicts verdicts})})))))))

;; ---------------------------------------------------------------------------
;; Minimization lower-bound verification: the minimization analogue of
;; :universal-reported-bound. Its target bounds the ORIGINAL cost (the standard form
;; with the original margins as the cost row), not the negated universal endpoint,
;; so it is reconstructed separately -- here, never taken from the producer.
(defn- expected-minimization-lower-type [instance lower]
  (let [standard (#'lp/standard-form instance)
        {:keys [b rows cols row-activity zero-on objective]}
        (#'lp/instance-terms (assoc standard :margins (:margins instance)))
        lower-term (#'lp/signed-literal lower)]
    (f/forall [['candidate (f/arrow lp/nat lp/signed)]
               ['feasible (all-at-most (row-activity 'candidate) b rows)]
               ['nonnegative (all-at-most (zero-on) 'candidate cols)]]
              (app 'signed/at-most lower-term (objective 'candidate)))))

(defn- validate-minimization! [instance lower reductions]
  (when-not (and (map? instance) (= :minimize (:sense instance)))
    (refuse! :lp-minimization/wrong-sense "A minimization instance is required"))
  (validate-budget! reductions)
  (when-not (and (bounded-lp-data? instance) (bounded-exact? lower))
    (refuse! :lp-report/input-shape
             "Expected bounded exact minimization data and lower bound")))

(defn verify-minimization-lower-bound
  "Independently verify a reported lower bound L for a minimization instance:
  for EVERY feasible, nonnegative candidate, L <= original cost. The universally
  quantified target is reconstructed from the instance and L (never the producer)
  and the supplied proof value is replayed fail-closed and axiom-free. Same limits
  as verify-report; the standard-form interpretation and literal encoding remain
  trusted, and submitted-plan feasibility / constraint expansion stay host
  boundaries."
  ([env instance lower proof] (verify-minimization-lower-bound env instance lower proof {}))
  ([env instance lower proof {:keys [reductions] :or {reductions 500000}}]
   (fail-closed
    (fn []
      (validate-minimization! instance lower reductions)
      (let [instance (select-keys instance instance-fields)
            type (expected-minimization-lower-type instance lower)
            r (replay-one env reductions proof type)]
        (if (= :checked (:status r))
          {:status :minimization-bound-verified :orientation :minimization
           :lower lower :verdict r
           :audit/id (canonical/content-id {:schema :lp-minimization/v1
                                            :instance instance :lower lower :verdict r})}
          {:status (:status r) :error/category (:error/category r)}))))))

(defn verify-report
  "Replay ALL four proof values in a supplied already-checked environment.
  Returns :report-verified only for exact coverage and four axiom-free checks.
  Report status, proof-supplied target types and solver success flags are not used.
  Extra instance/report metadata is outside the verified projection and identity.

  Limits: <=32 columns/expanded rows; exact scalar numerator magnitude and
  denominator <=10000; fuel <=1e6 PER normalization, not a total time/memory cap.
  No hostile-input process isolation, proof-size bound, or production guarantee.
  Original standard-form interpretation and literal encoding remain trusted."
  ([env instance report proofs] (verify-report env instance report proofs {}))
  ([env instance report proofs {:keys [reductions] :or {reductions 500000}}]
   (fail-closed
    (fn []
      (validate! instance report proofs reductions)
      (let [instance (select-keys instance instance-fields)
            report (select-keys report report-fields)
            types (expected-types instance report)]
        (replay-all
         env reductions proofs types required-obligations
         (fn [verdicts]
           {:status :report-verified :scope :original-standard-form-report-relations
            :required-obligations required-obligations :verdicts verdicts
            :orientation (if (= :minimize (:sense instance)) :negated-minimization :maximization)
            :audit/id (canonical/content-id {:schema :lp-report/v1 :instance instance
                                             :report report :verdicts verdicts})})))))))
