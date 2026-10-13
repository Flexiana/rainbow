(ns rainbow.math.rational.signed.strict-convex-unique
  "Uniqueness of the minimizer for a strictly convex function -- the OR-Commons payoff of the
  convexity lane: a strictly convex objective has at most one minimizer (up to equivalence).
     signed/is-minimizer f x := forall z, f x <= f z
     signed/strict-convex-minimizer-unique :
       strict-convex-on f -> is-minimizer f x -> is-minimizer f y
       -> 0 < w0 -> 0 < w1 -> (w0 + w1 ~ 1) -> not(x ~ y) -> falsity.
  Proof: strict convexity at (w0,w1) gives f(wsum) < wsum(f x, f y); both minima are equal
  (antisymmetry) so wsum collapses to f x; but f x <= f(wsum), so f(wsum) < f(wsum) -- absurd.
  Stated over ABSTRACT positive weights (any convex-combination witness), so the check is symbolic."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.square-strict-convex :as strict-convex]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-fn (function/arrow signed signed))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nn-lt [a b] (app (function/const* 'nnrat/less-than []) a b))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(def ^:private falsity (function/const* 'proposition/falsity []))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- etr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- addresp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- mlre [a b c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) a b c h))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- dist-add-right [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- fnn-add [a b] (app (function/const* 'signed/from-nnrat-add []) a b))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- at-most-antisym [a b ab ba] (app (function/const* 'signed/at-most-antisymmetric []) a b ab ba))
(defn- at-most-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- leresp [a ah b bh ha hb ord] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh ha hb ord))
(defn- llla [x y z hxy hle] (app (function/const* 'signed/less-than-of-less-than-of-at-most []) x y z hxy hle))
(defn- lt-irrefl [x] (app (function/const* 'signed/less-than-irreflexive []) x))
(defn- strict-cvx-on [f] (app (function/const* 'signed/strict-convex-on []) f))

(defn- wsum [w0 w1 a b] (sadd (smul (fnn w0) a) (smul (fnn w1) b)))

;; wsum w0 w1 B B ~ B  when w0+w1 ~ 1 (replicated from signed-convex-function).
(defn- weights-collapse [w0 w1 B hw]
  (etr (sadd (smul (fnn w0) B) (smul (fnn w1) B)) (smul (fnn (radd w0 w1)) B) B
       (etr (sadd (smul (fnn w0) B) (smul (fnn w1) B))
            (smul (sadd (fnn w0) (fnn w1)) B) (smul (fnn (radd w0 w1)) B)
            (esym (smul (sadd (fnn w0) (fnn w1)) B)
                  (sadd (smul (fnn w0) B) (smul (fnn w1) B))
                  (dist-add-right (fnn w0) (fnn w1) B))
            (mrre (sadd (fnn w0) (fnn w1)) (fnn (radd w0 w1)) B (fnn-add w0 w1)))
       (etr (smul (fnn (radd w0 w1)) B) (smul (fnn rone) B) B
            (mrre (fnn (radd w0 w1)) (fnn rone) B (fnn-resp (radd w0 w1) rone hw))
            (one-left B))))

;; is-minimizer f x := forall z, f x <= f z
(def is-minimizer-spec
  {:name 'signed/is-minimizer
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow sig-fn (function/arrow signed 'Prop))
   :value (function/lam [['f sig-fn] ['x signed]]
                        (function/forall [['z signed]] (sle (function/app 'f 'x) (function/app 'f 'z))))})

(defn- is-min [f x] (app (function/const* 'signed/is-minimizer []) f x))

(def minimizer-unique-spec
  {:name 'signed/strict-convex-minimizer-unique
   :universes []
   :type (function/forall
          [['f sig-fn] ['x signed] ['y signed] ['w0 nnrat] ['w1 nnrat]
           ['hf (strict-cvx-on 'f)] ['hx (is-min 'f 'x)] ['hy (is-min 'f 'y)]
           ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
           ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
          falsity)
   :value
   (function/lam
    [['f sig-fn] ['x signed] ['y signed] ['w0 nnrat] ['w1 nnrat]
     ['hf (strict-cvx-on 'f)] ['hx (is-min 'f 'x)] ['hy (is-min 'f 'y)]
     ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
     ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
    (let [fx (function/app 'f 'x) fy (function/app 'f 'y)
          mid (wsum 'w0 'w1 'x 'y)
          fmid (function/app 'f mid)
          strict (app 'hf 'w0 'w1 'x 'y 'hw0 'hw1 'hw 'hxy)   ; f(mid) < wsum w0 w1 fx fy
          fxy (at-most-antisym fx fy (app 'hx 'y) (app 'hy 'x))            ; f x ~ f y
          hf-fx (smul (fnn 'w0) fx) hf-fy (smul (fnn 'w1) fy)
          swap (mlre fy fx (fnn 'w1) (esym fx fy fxy))                     ; (fnn w1)*fy ~ (fnn w1)*fx
          collapse1 (addresp hf-fx hf-fx hf-fy (smul (fnn 'w1) fx) (erefl hf-fx) swap) ; wsum fx fy ~ wsum fx fx
          collapse2 (weights-collapse 'w0 'w1 fx 'hw)                      ; wsum fx fx ~ fx
          collapse (etr (wsum 'w0 'w1 fx fy) (wsum 'w0 'w1 fx fx) fx collapse1 collapse2)
          wsum-le-fx (leresp fx (wsum 'w0 'w1 fx fy) fx fx
                             (esym (wsum 'w0 'w1 fx fy) fx collapse) (erefl fx) (at-most-refl fx))
          fmid-lt-fx (llla fmid (wsum 'w0 'w1 fx fy) fx strict wsum-le-fx)
          fx-le-mid (app 'hx mid)                                          ; f x <= f(mid)
          self (llla fmid fx fmid fmid-lt-fx fx-le-mid)]                   ; f(mid) < f(mid)
      (app (lt-irrefl fmid) self)))})

(def theorem-specs [is-minimizer-spec minimizer-unique-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      strict-convex/extend-environment
      (support/extend-with :signed-strict-convex-unique theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
