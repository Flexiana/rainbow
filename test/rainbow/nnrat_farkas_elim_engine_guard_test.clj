(ns rainbow.nnrat-farkas-elim-engine-guard-test
  "Regression guard over the CLASSIC Fourier-Motzkin elimination engine, the
  n-variable machinery the LP-duality program rests on.

  The vacuity audit found the empty-list
  vacuity confined to the partition layer; the classic engine states solvability
  as EXISTS a solution VALUE and proves iffs about it, and a comprehensive pass
  found NONE of its theorems passthrough-inhabited. This test freezes that: it
  auto-enumerates every theorem of the nine elimination modules and asserts that
  returning any one of a theorem's own hypotheses does NOT inhabit its
  conclusion (a necessary condition for non-vacuity: the conclusion is not defeq
  a hypothesis).

  Polarity is NORMAL: PASS = the engine still resists passthrough (good). A
  FAILURE names an engine theorem whose conclusion became defeq a hypothesis --
  i.e. weakened to triviality. Auto-enumeration means new engine theorems are
  covered automatically. This guards ONE vacuity mode (conclusion == hypothesis)
  -- a necessary check, not a proof of substantiveness (see the report's
  method-asymmetry note). Tests only; no proved brick edited, no direction
  picked."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.farkas-elim-chain :as elim-chain]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as elim-coupled]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim-list]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as elim-affine-list]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list-lower :as elim-affine-list-lower]
            [rainbow.math.rational.nnrat.farkas-elim-affine-coupled :as elim-affine-coupled]
            [rainbow.math.rational.nnrat.farkas-elim-scaled-coupled :as elim-scaled-coupled]
            [rainbow.math.rational.nnrat.farkas-elim-scaled-coupled-lower :as elim-scaled-coupled-lower]
            [rainbow.math.rational.nnrat.farkas-elim-two-var :as elim-two-var]))

;; the theorem-ids accessor of each engine module (explicit -> legible, no reflection)
(def ^:private engine-theorem-id-fns
  [elim-chain/theorem-ids elim-coupled/theorem-ids elim-list/theorem-ids
   elim-affine-list/theorem-ids elim-affine-list-lower/theorem-ids
   elim-affine-coupled/theorem-ids elim-scaled-coupled/theorem-ids
   elim-scaled-coupled-lower/theorem-ids elim-two-var/theorem-ids])

;; extend the checkpoint with every engine module (explicit, so it is legible)
(def ^:private engine-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          elim-chain/extend-environment
          elim-coupled/extend-environment
          elim-list/extend-environment
          elim-affine-list/extend-environment
          elim-affine-list-lower/extend-environment
          elim-affine-coupled/extend-environment
          elim-scaled-coupled/extend-environment
          elim-scaled-coupled-lower/extend-environment
          elim-two-var/extend-environment))))

(defn- engine-theorem-names [env]
  (sort (distinct (mapcat (fn [f] (keys (f env))) engine-theorem-id-fns))))

(defn- pi-domains [t]
  (loop [t t ds []]
    (if (and (vector? t) (= :pi (first t))) (recur (nth t 2) (conj ds (nth t 1))) ds)))

(defn- mk-lam [domains body]
  (reduce (fn [b d] [:lam d b :explicit]) body (reverse domains)))

(defn- passthrough-checks? [env t i n]
  (= :checked (:status (kernel/check env (mk-lam (pi-domains t) [:bound (dec (- n i))]) t #{}))))

(deftest elimination-engine-rejects-passthrough
  (testing "no theorem of the classic elimination engine is inhabited by
            returning one of its own hypotheses. A FAILURE names an engine
            theorem that was weakened to triviality (conclusion became defeq a
            hypothesis)."
    (let [env @engine-environment
          names (engine-theorem-names env)]
      (is (pos? (count names)) "no engine theorems enumerated -- module wiring changed")
      (doseq [nm names]
        (let [t (:rainbow/type (environment/declaration env (environment/resolve-id env nm)))
              n (count (pi-domains t))]
          (doseq [i (range n)]
            (is (not (passthrough-checks? env t i n))
                (str nm ": returning argument " i " now inhabits the conclusion "
                     "-- the conclusion became defeq that hypothesis, so the "
                     "theorem was weakened to triviality. Check the change "
                     "against the design notes."))))))))
