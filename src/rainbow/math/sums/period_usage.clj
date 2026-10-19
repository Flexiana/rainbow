(ns rainbow.math.sums.period-usage
  "Multiplying two Boolean indicators by a weight equals filtering that weight by both tests."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call mul eqv]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def U [:succ [:zero]])
(def bool (f/const* 'data/Bool []))
(def false-bit (f/const* 'data/false [])) (def true-bit (f/const* 'data/true []))
(defn selected [no yes bit]
  (let [ignored (gensym "ignored")] (f/app (f/const* 'data/Bool.rec [U]) (f/lam [[ignored bool]] signed) no yes bit)))
(defn bit [choice] (selected s/zero b/one choice))
(defn value [a b r] (selected s/zero (selected s/zero r b) a))
(def weight-spec
  (let [A 'A B 'B r 'r goal (fn [aa bb] (eqv (mul (mul (bit aa) (bit bb)) r) (value aa bb r)))]
    (s/spec 'signed/two-indicator-weight-is-filtered [[A bool] [B bool] [r signed]] (goal A B)
      (f/app (f/const* 'data/Bool.rec [[:zero]]) (f/lam [['outer bool]] (goal 'outer B))
        (f/app (f/const* 'data/Bool.rec [[:zero]]) (f/lam [['inner bool]] (goal false-bit 'inner))
          (a/ring-eq (mul (mul s/zero s/zero) r) s/zero)
          (a/ring-eq (mul (mul s/zero b/one) r) s/zero) B)
        (f/app (f/const* 'data/Bool.rec [[:zero]]) (f/lam [['inner bool]] (goal true-bit 'inner))
          (a/ring-eq (mul (mul b/one s/zero) r) s/zero)
          (a/ring-eq (mul (mul b/one b/one) r) r) B)
        A))))
(def theorem-specs [weight-spec])
(def deps '[rainbow.math.sums.lp-bounds])
(defn install [env] (support/extend-with env :expr-sum-period-usage theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.period-usage))
