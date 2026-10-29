(ns rainbow.math.rational.signed.lp-plan-report-bridge
  "Original submitted-plan/report evidence and optional tight-bound optimality.
  Producer only: no status decision, verifier policy or executable-correctness claim."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-original-bound-bridge :as bound]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def zero (f/const* 'signed/zero []))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- le [a b] (app 'signed/at-most a b))
(defn- bounded? [x]
  (and (or (integer? x) (ratio? x))
       (<= -10000 (if (ratio? x) (numerator x) x) 10000)
       (<= 1 (if (ratio? x) (denominator x) 1) 10000)))
(defn- literal [x] (#'lp/signed-literal x))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv literal xs))
      (f/lam [['index lp/nat]] zero)))
(defn- dot [a x columns]
  (let [m (mapping a)]
    (poly 'signed/map-sum lp/nat
          (f/lam [['i lp/nat]] (app 'signed/multiply (f/app m 'i) (f/app x 'i))) columns)))
(defn- conjoin-specs [specs]
  (reduce (fn [tail head]
            {:type (app 'proposition/conjunction (:type head) (:type tail))
             :value (app 'proposition/conjoin (:type head) (:type tail) (:value head) (:value tail))})
          {:type (f/const* 'proposition/truth []) :value (f/const* 'proposition/trivial [])}
          (reverse specs)))
(defn- validate! [original report]
  (when-not (and (map? report) (= #{:achieved :bound :gap :direction} (set (keys report)))
                 (= (:direction report) (if (= :minimize (:sense original)) :lower :upper))
                 (every? bounded? ((juxt :achieved :bound :gap) report))
                 (vector? (:plan original)) (vector? (:margins original))
                 (= (count (:plan original)) (count (:margins original)))
                 (every? bounded? (:plan original)))
    (throw (ex-info "Expected bounded exact original plan and exact report fields/direction"
                    {:error/category :lp-plan-report/domain}))))

(defn plan-report-specs
  "Eleven obligations: six original-bound specs plus original plan feasibility,
  achieved-value binding, oriented reported gap, gap nonnegativity and numeric order.
  Certifies original[:plan], NOT actual[:plan]. A valid bound alone does not assert
  this plan feasible. A nonzero gap may pass here; optimality is a separate API."
  [original actual report]
  (validate! original report)
  (let [specs (bound/original-bound-specs original actual (:bound report))
        x (mapping (:plan original)) cols (#'lp/index-list (count (:plan original)))
        clause (fn [equality? coefficients rhs]
                 (let [activity (dot coefficients x cols) b (literal rhs)]
                   {:type ((if equality? eqv le) activity b)
                    :value ((if equality? #'lp/computed-equivalence #'lp/decided-at-most) activity b)}))
        constraints (conjoin-specs
                     (concat (map #(clause false %1 %2) (:matrix original) (:capacities original))
                             (map #(clause true (:row %) (:value %)) (:equalities original))))
        zero-on (f/lam [['ignored lp/nat]] zero)
        nn (poly 'signed/all-at-most lp/nat zero-on x cols)
        feasible {:type (app 'proposition/conjunction (:type constraints) nn)
                  :value (app 'proposition/conjoin (:type constraints) nn (:value constraints)
                              (#'lp/all-at-most-proof zero-on x (count (:plan original))))}
        objective (dot (:margins original) x cols)
        A (literal (:achieved report)) B (literal (:bound report)) G (literal (:gap report))
        achieved {:type (eqv objective A) :value (#'lp/computed-equivalence objective A)}
        minimum? (= :minimize (:sense original))
        gap-left (if minimum? A B)
        gap-right (app 'signed/add (if minimum? B A) G)
        actual-bound (f/app (:value (:universal-original-bound specs)) x (:value feasible))
        order-proof (if minimum?
                      (app 'signed/at-most-respects-equivalence B B objective A
                           (app 'signed/equivalent-reflexive B) (:value achieved) actual-bound)
                      (app 'signed/at-most-respects-equivalence objective A B B
                           (:value achieved) (app 'signed/equivalent-reflexive B) actual-bound))]
    (assoc specs
           :submitted-plan-feasible feasible
           :achieved-value achieved
           :reported-gap {:type (eqv gap-left gap-right) :value (#'lp/computed-equivalence gap-left gap-right)}
           :gap-nonnegative {:type (le zero G) :value (#'lp/decided-at-most zero G)}
           :reported-order {:type (if minimum? (le B A) (le A B)) :value order-proof})))

(defn optimality-specs
  "Add tight-endpoint and full original-model optimality to the eleven report specs.
  Optimality includes plan feasibility AND no feasible candidate being better.
  This sufficient certificate requires achieved~bound, not a host gap==0 flag.
  False tightness produces kernel-rejected evidence, not a suboptimality verdict."
  [original actual report]
  (let [specs (plan-report-specs original actual report)
        universal (:universal-original-bound specs)
        ;; Internal producer composition only; receiver reconstructs original
        ;; feasibility and objective independently from its own request data.
        bindings (second (:type universal))
        x (mapping (:plan original)) cols (#'lp/index-list (count (:plan original)))
        candidate-objective (dot (:margins original) 'candidate cols)
        plan-objective (dot (:margins original) x cols)
        A (literal (:achieved report)) B (literal (:bound report))
        tight {:type (eqv A B) :value (#'lp/computed-equivalence A B)}
        endpoint (app 'signed/equivalent-transitive plan-objective A B
                      (:value (:achieved-value specs)) (:value tight))
        reverse-endpoint (app 'signed/equivalent-symmetric plan-objective B endpoint)
        bounded (f/app (:value universal) 'candidate 'original-feasible)
        minimum? (= :minimize (:sense original))
        order (if minimum? (le plan-objective candidate-objective) (le candidate-objective plan-objective))
        order-proof
        (if minimum?
          (app 'signed/at-most-respects-equivalence B plan-objective candidate-objective candidate-objective
               reverse-endpoint (app 'signed/equivalent-reflexive candidate-objective) bounded)
          (app 'signed/at-most-respects-equivalence candidate-objective candidate-objective B plan-objective
               (app 'signed/equivalent-reflexive candidate-objective) reverse-endpoint bounded))
        all-candidates (f/forall bindings order)
        feasible (:submitted-plan-feasible specs)]
    (assoc specs :tight-endpoint tight
           :optimality {:type (app 'proposition/conjunction (:type feasible) all-candidates)
                        :value (app 'proposition/conjoin (:type feasible) all-candidates
                                    (:value feasible) (f/lam bindings order-proof))})))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-original-bound-bridge])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-plan-report-bridge))
