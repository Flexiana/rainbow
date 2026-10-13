(ns rainbow.math.rational.nnrat.strict-order
  "Strict order on nonnegative rationals -- the nnrat mirror of signed_strict_order, needed for
  the no-zero-divisors pair theorem (which case-splits on the nnrat order of a signed value's
  positive/negative components).

    nnrat/less-than x y := (at-most x y) AND (not (equivalent x y))   [reducible]
    + intro, implies-at-most, irreflexive, asymmetric, transitive, and the two <=/< mixing lemmas.

  Direct port of the signed strict order onto the nnrat order primitives. Wall-free."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.algorithms.proofs.decision-guarantee-audit :as order]
            [rainbow.math.finite.policy-iteration :as respects]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private prop 'Prop)
(defn- app [f & a] (apply function/app f a))
(defn- nle [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- neqv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'nnrat/equivalent-reflexive []) x))
(defn- antisym [a b ab ba] (app (function/const* 'nnrat/at-most-antisymmetric []) a b ab ba))
(defn- le-trans [a b c h1 h2] (app (function/const* 'nnrat/at-most-transitive []) a b c h1 h2))
(defn- le-refl [x] (app (function/const* 'nnrat/at-most-reflexive []) x))
(defn- nn-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
;; nnrat at-most-respects (MIRROR of signed): (L eL R eR)(L~eL)(R~eR)(eL<=eR) : L<=R
(defn- nn-resp [L eL R eR sL sR ord] (app (function/const* 'nnrat/at-most-respects-equivalence []) L eL R eR sL sR ord))
(defn- pconj [l r] (app (function/const* 'proposition/conjunction []) l r))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(defn- pconjoin [l r le re] (app (function/const* 'proposition/conjoin []) l r le re))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- lt [x y] (app (function/const* 'nnrat/less-than []) x y))
(defn- lt-le [x y h] (pleft (nle x y) (pneg (neqv x y)) h))
(defn- lt-neq [x y h] (pright (nle x y) (pneg (neqv x y)) h))
(defn- le-of-equiv-rev [x z exz] (nn-resp z x x x (nn-sym x z exz) (erefl x) (le-refl x)))  ; z<=x from x~z

(def less-than-spec
  {:name 'nnrat/less-than :kind :definition :transparency :reducible :universes []
   :type (function/arrow nnrat (function/arrow nnrat prop))
   :value (function/lam [['x nnrat] ['y nnrat]] (pconj (nle 'x 'y) (pneg (neqv 'x 'y))))})

(def less-than-intro-spec
  {:name 'nnrat/less-than-intro :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['le (nle 'x 'y)] ['neq (pneg (neqv 'x 'y))]] (lt 'x 'y))
   :value (function/lam [['x nnrat] ['y nnrat] ['le (nle 'x 'y)] ['neq (pneg (neqv 'x 'y))]]
                        (pconjoin (nle 'x 'y) (pneg (neqv 'x 'y)) 'le 'neq))})

(def less-than-implies-at-most-spec
  {:name 'nnrat/less-than-implies-at-most :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['h (lt 'x 'y)]] (nle 'x 'y))
   :value (function/lam [['x nnrat] ['y nnrat] ['h (lt 'x 'y)]] (lt-le 'x 'y 'h))})

(def less-than-irreflexive-spec
  {:name 'nnrat/less-than-irreflexive :universes []
   :type (function/forall [['x nnrat]] (pneg (lt 'x 'x)))
   :value (function/lam [['x nnrat]]
                        (function/lam [['h (lt 'x 'x)]] (app (lt-neq 'x 'x 'h) (erefl 'x))))})

(def less-than-asymmetric-spec
  {:name 'nnrat/less-than-asymmetric :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['hxy (lt 'x 'y)]] (pneg (lt 'y 'x)))
   :value (function/lam [['x nnrat] ['y nnrat] ['hxy (lt 'x 'y)]]
                        (function/lam [['hyx (lt 'y 'x)]]
                                      (app (lt-neq 'x 'y 'hxy)
                                           (antisym 'x 'y (lt-le 'x 'y 'hxy) (lt-le 'y 'x 'hyx)))))})

(def less-than-transitive-spec
  {:name 'nnrat/less-than-transitive :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['z nnrat] ['hxy (lt 'x 'y)] ['hyz (lt 'y 'z)]] (lt 'x 'z))
   :value (function/lam [['x nnrat] ['y nnrat] ['z nnrat] ['hxy (lt 'x 'y)] ['hyz (lt 'y 'z)]]
                        (pconjoin (nle 'x 'z) (pneg (neqv 'x 'z))
                                  (le-trans 'x 'y 'z (lt-le 'x 'y 'hxy) (lt-le 'y 'z 'hyz))
                                  (function/lam [['exz (neqv 'x 'z)]]
                                                (app (lt-neq 'x 'y 'hxy)
                                                     (antisym 'x 'y (lt-le 'x 'y 'hxy)
                                                              (le-trans 'y 'z 'x (lt-le 'y 'z 'hyz)
                                                                        (le-of-equiv-rev 'x 'z 'exz)))))))})

(def less-than-of-at-most-of-less-than-spec
  {:name 'nnrat/less-than-of-at-most-of-less-than :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['z nnrat] ['hle (nle 'x 'y)] ['hyz (lt 'y 'z)]] (lt 'x 'z))
   :value (function/lam [['x nnrat] ['y nnrat] ['z nnrat] ['hle (nle 'x 'y)] ['hyz (lt 'y 'z)]]
                        (pconjoin (nle 'x 'z) (pneg (neqv 'x 'z))
                                  (le-trans 'x 'y 'z 'hle (lt-le 'y 'z 'hyz))
                                  (function/lam [['exz (neqv 'x 'z)]]
                                                (app (lt-neq 'y 'z 'hyz)
                                                     (antisym 'y 'z (lt-le 'y 'z 'hyz)
                                                              (le-trans 'z 'x 'y (le-of-equiv-rev 'x 'z 'exz) 'hle))))))})

(def less-than-of-less-than-of-at-most-spec
  {:name 'nnrat/less-than-of-less-than-of-at-most :universes []
   :type (function/forall [['x nnrat] ['y nnrat] ['z nnrat] ['hxy (lt 'x 'y)] ['hle (nle 'y 'z)]] (lt 'x 'z))
   :value (function/lam [['x nnrat] ['y nnrat] ['z nnrat] ['hxy (lt 'x 'y)] ['hle (nle 'y 'z)]]
                        (pconjoin (nle 'x 'z) (pneg (neqv 'x 'z))
                                  (le-trans 'x 'y 'z (lt-le 'x 'y 'hxy) 'hle)
                                  (function/lam [['exz (neqv 'x 'z)]]
                                                (app (lt-neq 'x 'y 'hxy)
                                                     (antisym 'x 'y (lt-le 'x 'y 'hxy)
                                                              (le-trans 'y 'z 'x 'hle (le-of-equiv-rev 'x 'z 'exz)))))))})

(def theorem-specs
  [less-than-spec less-than-intro-spec less-than-implies-at-most-spec
   less-than-irreflexive-spec less-than-asymmetric-spec less-than-transitive-spec
   less-than-of-at-most-of-less-than-spec less-than-of-less-than-of-at-most-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      metric/extend-environment
      order/extend-environment
      respects/extend-environment
      (support/extend-with :nnrat-strict-order theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
