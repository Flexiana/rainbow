(ns rainbow.math.rational.signed.lp-original-bound-bridge
  "Universal original-problem bounds, including original equality constraints.
  Untrusted producer: all target reconstruction/checking belongs to the receiver.
  Actual expanded rows, objective coefficients and prices stay explicit."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-feasibility-bridge :as feasibility]
            [rainbow.math.rational.signed.lp-equality-row-bridge :as row]
            [rainbow.math.rational.signed.lp-objective-negate :as sense]
            [rainbow.math.rational.signed.lp-duality-on :as duality]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def zero (f/const* 'signed/zero []))
(defn- neg [a] (app 'signed/negate a))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- le [a b] (app 'signed/at-most a b))
(defn- bounded? [x]
  (and (or (integer? x) (ratio? x))
       (<= -10000 (if (ratio? x) (numerator x) x) 10000)
       (<= 1 (if (ratio? x) (denominator x) 1) 10000)))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
      (f/lam [['index lp/nat]] zero)))
(defn- sum [m indices] (poly 'signed/map-sum lp/nat m indices))
(defn- products [a x]
  (f/lam [['i lp/nat]] (app 'signed/multiply (f/app a 'i) (f/app x 'i))))
(defn- all-le [a b indices] (poly 'signed/all-at-most lp/nat a b indices))

(defn original-bound-specs
  "Six required evidence specs, ending in a bound for EVERY originally feasible x.
  Original sense selects upper(max/nil) or lower(min). Actual must already be
  expanded and have maximization-oriented coefficients; it is not standardized
  again here. Endpoint may be looser than the dual objective, if its inequality
  checks. Plan and original dual prices are not used or asserted correct."
  [original actual endpoint]
  (when-not (contains? #{nil :maximize :minimize} (:sense original))
    (throw (ex-info "Unsupported original objective sense" {:error/category :lp-original-bound/sense})))
  (when-not (and (vector? (:margins original)) (vector? (:margins actual))
                 (vector? (:prices actual))
                 (= (count (:prices actual)) (count (:capacities actual)))
                 (every? bounded? (concat (:margins original) (:margins actual) (:prices actual) [endpoint])))
    (throw (ex-info "Expected bounded exact objectives, actual prices and endpoint"
                    {:error/category :lp-original-bound/domain})))
  (let [whole (:primal-feasibility-equivalence (feasibility/feasibility-specs original actual))
        ;; Internal untrusted proof composition only. A receiver MUST reconstruct
        ;; its original predicate independently, never take this declared type on trust.
        original-primal (nth (nth (:type whole) 2) 2)
        minimizing? (= :minimize (:sense original))
        cols (#'lp/index-list (count (:margins original)))
        rows (#'lp/index-list (count (:capacities actual)))
        M (if (seq (:matrix actual))
            (#'lp/nat-lookup (f/arrow lp/nat lp/signed) (mapv mapping (:matrix actual)))
            (f/lam [['row-index lp/nat]] (mapping [])))
        b (mapping (:capacities actual)) c (mapping (:margins actual))
        oc (mapping (:margins original)) y (mapping (:prices actual))
        zero-on (f/lam [['ignored lp/nat]] zero)
        activity (f/lam [['i lp/nat]]
                        (sum (f/lam [['j lp/nat]]
                                    (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app 'candidate 'j))) cols))
        dual-price (f/lam [['j lp/nat]]
                          (sum (f/lam [['i lp/nat]]
                                      (app 'signed/multiply (f/app (f/app M 'i) 'j) (f/app y 'i))) rows))
        actual-feasible (all-le activity b rows)
        candidate-nn (all-le zero-on 'candidate cols)
        actual-primal (app 'proposition/conjunction actual-feasible candidate-nn)
        translated (app 'proposition/equivalence-forward original-primal actual-primal
                        (f/app (:value whole) 'candidate) 'original-feasible)
        d {:type (all-le c dual-price cols)
           :value (#'lp/all-at-most-proof c dual-price (count (:margins actual)))}
        yn {:type (all-le zero-on y rows)
            :value (#'lp/all-at-most-proof zero-on y (count (:prices actual)))}
        Q (sum (products b y) rows)
        E (#'lp/signed-literal endpoint)
        SE (#'lp/signed-literal (if minimizing? (- endpoint) endpoint))
        qe {:type (le Q SE) :value (#'lp/decided-at-most Q SE)}
        table (if minimizing?
                (:negative-coefficients
                 (row/row-pair-specs (:margins original) 0 (:margins original) 0 (:margins actual) 0))
                (:coefficients (row/inequality-row-specs (:margins original) 0 (:margins actual) 0)))
        expected-c (if minimizing? (f/lam [['i lp/nat]] (neg (f/app oc 'i))) oc)
        S (sum (products c 'candidate) cols)
        F (sum (products expected-c 'candidate) cols)
        O (sum (products oc 'candidate) cols)
        SO (if minimizing? (neg O) O)
        correspondence
        (poly 'signed/map-sum-respects-equivalence lp/nat (products c 'candidate) (products expected-c 'candidate)
              (f/lam [['i lp/nat]]
                     (app 'signed/multiply-right-respects-equivalence
                          (f/app c 'i) (f/app expected-c 'i) (f/app 'candidate 'i)
                          (f/app (:value table) 'i))) cols)
        object-same (if minimizing?
                      (app 'signed/equivalent-transitive S F SO correspondence
                           (poly 'signed/lp-objective-negate lp/nat oc 'candidate cols))
                      correspondence)
        weak (poly 'optimization/signed-lp-weak-duality-on lp/nat lp/nat M b c 'candidate y rows cols
                   (app 'proposition/left actual-feasible candidate-nn translated) (:value d)
                   (app 'proposition/right actual-feasible candidate-nn translated) (:value yn))
        upper (app 'signed/at-most-transitive S Q SE weak (:value qe))
        original-oriented-upper
        (app 'signed/at-most-respects-equivalence S SO SE (if minimizing? (neg E) E)
             object-same (#'lp/computed-equivalence SE (if minimizing? (neg E) E)) upper)
        bound-proof (if minimizing?
                      (app 'signed/at-most-respects-equivalence (neg (neg E)) E (neg (neg O)) O
                           (app 'signed/negate-involutive E) (app 'signed/negate-involutive O)
                           (app 'signed/negate-reverses-order (neg O) (neg E) original-oriented-upper))
                      original-oriented-upper)
        cb [['candidate (f/arrow lp/nat lp/signed)]]]
    (array-map
     :primal-feasibility-equivalence whole
     :objective-correspondence {:type (f/forall cb (eqv S SO)) :value (f/lam cb object-same)}
     :dual-feasibility d :dual-nonnegative yn :dual-endpoint-bound qe
     :universal-original-bound
     {:type (f/forall (conj cb ['original-feasible original-primal])
                      (if minimizing? (le E O) (le O E)))
      :value (f/lam (conj cb ['original-feasible original-primal]) bound-proof)})))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-feasibility-bridge rainbow.math.rational.signed.lp-duality-on rainbow.math.rational.signed.lp-objective-negate rainbow.math.rational.signed.decide-order])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-original-bound-bridge))
