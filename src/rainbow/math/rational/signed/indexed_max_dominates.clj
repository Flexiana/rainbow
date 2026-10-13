(ns rainbow.math.rational.signed.indexed-max-dominates
  "Full dominance for the index-aware max: every index below n is bounded by the aggregate.
     signed/indexed-max-from-dominates :
       forall env init n i, strict-below i n -> env i <= indexed-max-from env init n.
  The argmax semantic property in full. By induction on n: n=0 is vacuous (strict-below i 0 is
  refuted); n=succ m splits strict-below i (succ m) via nat/strict-below-successor-split into
  (i < m -> use IH, then max-upper-left) or (i = m -> max-upper-right, transported along i=m).
  Off the trusted base (a property of the self-contained indexed-max aggregation)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.indexed-max :as imax]
            [rainbow.math.nat.strict-below-split :as split]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private prop-level [:zero])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private environment-type (function/arrow nat signed))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- add [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- symm [a b h] (app (function/const* 'equality/symmetric [ulvl]) nat a b h))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- zero-not-succ [v] (app (function/const* 'nat/zero-not-successor []) v))
(defn- strict-below [v u] (app (function/const* 'nat/strict-below []) v u))
(defn- sb-split [i m h] (app (function/const* 'nat/strict-below-successor-split []) i m h))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- at-most-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- max-upper-left [a b] (app (function/const* 'signed/max-upper-left []) a b))
(defn- max-upper-right [a b] (app (function/const* 'signed/max-upper-right []) a b))
(defn- imax-from [env init n] (app (function/const* 'signed/indexed-max-from []) env init n))
(defn- explode [result imp] (app (function/const* 'proposition/explode []) result imp))
(defn- use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))

(def dominates-spec
  {:name 'signed/indexed-max-from-dominates
   :universes []
   :type (function/forall
          [['env environment-type] ['init signed] ['n nat] ['i nat]
           ['h (strict-below 'i 'n)]]
          (sle (app 'env 'i) (imax-from 'env 'init 'n)))
   :value
   (function/lam
    [['env environment-type] ['init signed] ['n nat] ['i nat] ['h (strict-below 'i 'n)]]
    (let [im (fn [k] (imax-from 'env 'init k))
          goal (fn [k idx] (sle (app 'env idx) (im k)))
          motive (function/lam [['k nat]]
                               (function/forall [['j nat] ['hj (strict-below 'j 'k)]] (goal 'k 'j)))
          base (function/lam
                [['j nat] ['hj (strict-below 'j nat-zero)]]
                ;; strict-below j 0 is impossible: (succ j)+extra = 0 defeq succ(...)=0
                (app 'hj (goal nat-zero 'j)
                     (function/lam
                      [['extra nat] ['pf (eqn (add (succ 'j) 'extra) nat-zero)]]
                      (explode (goal nat-zero 'j)
                               (app (zero-not-succ (add 'j 'extra))
                                    (symm (add (succ 'j) 'extra) nat-zero 'pf))))))
          stepfn (function/lam
                  [['m nat] ['ih (function/forall [['j nat] ['hj (strict-below 'j 'm)]] (goal 'm 'j))]]
                  (function/lam
                   [['j nat] ['hj (strict-below 'j (succ 'm))]]
                   (use-disj (strict-below 'j 'm) (eqn 'j 'm) (goal (succ 'm) 'j)
                             (sb-split 'j 'm 'hj)
                             ;; j < m : env j <= im m <= max(im m)(env m) = im (succ m)
                             (function/lam [['sb (strict-below 'j 'm)]]
                                           (at-most-trans (app 'env 'j) (im 'm) (im (succ 'm))
                                                          (app 'ih 'j 'sb)
                                                          (max-upper-left (im 'm) (app 'env 'm))))
                             ;; j = m : env m <= max(im m)(env m); transport env m -> env j
                             (function/lam [['eq (eqn 'j 'm)]]
                                           (subst 'm 'j (symm 'j 'm 'eq)
                                                  (function/lam [['t nat]] (sle (app 'env 't) (im (succ 'm))))
                                                  (max-upper-right (im 'm) (app 'env 'm)))))))]
      (app (function/app (function/const* 'data/Nat.rec [prop-level]) motive base stepfn 'n) 'i 'h)))})

(def theorem-specs [dominates-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      imax/extend-environment
      split/extend-environment
      (support/extend-with :signed-indexed-max-dominates theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
