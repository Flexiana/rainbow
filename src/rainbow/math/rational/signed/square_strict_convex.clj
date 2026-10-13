(ns rainbow.math.rational.signed.square-strict-convex
  "Strict convexity of the square, the capstone of the no-zero-divisors work:
     signed/strict-convex-on f := forall w0 w1 x y, 0<w0 -> 0<w1 -> (w0+w1 ~ 1) -> x !~ y ->
                                    f(wsum) < wsum(f x, f y)
     signed/square-strict-convex : strict-convex-on (\\x. x*x).
  Reuses signed/square-convex for the non-strict <= and the registered signed/variance-identity
  csq + w0*w1*(x-y)^2 ~ RHS. Strictness = the gap var = w0*w1*(x-y)^2 is nonzero: if csq ~ RHS then
  csq + var ~ csq, so var ~ 0 (equivalent-add-left-cancel), contradicting var !~ 0. The gap is
  nonzero by signed/multiply-nonzero on the (embedded, hence nonzero) weights and (x-y) !~ 0.
  Helper signed/from-nnrat-nonzero lifts nnrat w !~ 0 to fnn(w) !~ 0."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.square-convex :as square-convex]
            [rainbow.math.rational.signed.square-nonzero :as square-nonzero]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.nnrat.strict-order :as nnrat-strict]
            [rainbow.algorithms.proofs.counterfactual-distance-separation :as subtract-reflect]
            [rainbow.math.linear.matrix.least-squares-equality :as add-cancel]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-fn (function/arrow signed signed))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- slt [a b] (app (function/const* 'signed/less-than []) a b))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nn-lt [a b] (app (function/const* 'nnrat/less-than []) a b))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(def ^:private wsum-fn (function/lam [['x signed]] (smul 'x 'x)))
(defn- wsum [w0 w1 a b] (sadd (smul (fnn w0) a) (smul (fnn w1) b)))

;; signed/from-nnrat helpers
(defn- nnadd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-trans [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- nn-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- nn-azr [q] (app (function/const* 'nnrat/add-zero-right []) q))
(defn- nn-azl [q] (app (function/const* 'nnrat/add-zero-left []) q))

;; fnn(w) ~ 0 unfolds (defeq) to nnrat-equivalent (w + 0) (0 + 0); strip add-zeros -> w ~ 0.
(def from-nnrat-nonzero-spec
  {:name 'signed/from-nnrat-nonzero
   :universes []
   :type (function/forall [['w nnrat] ['hw (pneg (nn-equiv 'w nnzero))]]
                          (pneg (seqv (fnn 'w) szero)))
   :value
   (function/lam
    [['w nnrat] ['hw (pneg (nn-equiv 'w nnzero))]]
    (function/lam
     [['h (seqv (fnn 'w) szero)]]
     (app 'hw
          (nn-trans 'w (nnadd 'w nnzero) nnzero
                    (nn-sym (nnadd 'w nnzero) 'w (nn-azr 'w))
                    (nn-trans (nnadd 'w nnzero) (nnadd nnzero nnzero) nnzero
                              'h (nn-azl nnzero))))))})

(def strict-convex-on-spec
  {:name 'signed/strict-convex-on
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow sig-fn 'Prop)
   :value
   (function/lam
    [['f sig-fn]]
    (function/forall
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
      ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
     (slt (app 'f (wsum 'w0 'w1 'x 'y))
          (wsum 'w0 'w1 (app 'f 'x) (app 'f 'y)))))})

;; helper term-builders for the proof
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- etr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- addzr [a] (app (function/const* 'signed/add-zero-right []) a))
(defn- lt-intro [x y le neq] (app (function/const* 'signed/less-than-intro []) x y le neq))
(defn- variance-id [w0 w1 x y hw] (app (function/const* 'signed/variance-identity []) w0 w1 x y hw))
(defn- square-cvx [w0 w1 x y hw] (app (function/const* 'signed/square-convex []) w0 w1 x y hw))
(defn- mult-nonzero [a b ha hb] (app (function/const* 'signed/multiply-nonzero []) a b ha hb))
(defn- sq-nonzero [d hd] (app (function/const* 'signed/square-nonzero []) d hd))
(defn- from-nn-nonzero [w hw] (app (function/const* 'signed/from-nnrat-nonzero []) w hw))
(defn- sub-reflect [l r h] (app (function/const* 'signed/subtract-zero-reflects-equivalence []) l r h))
(defn- add-left-cancel [l r off h] (app (function/const* 'signed/equivalent-add-left-cancel []) l r off h))
(defn- nn-pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- nn-le [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- nn-esym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
;; from  0 < w  (defeq conjunction (0<=w)(not(0~w)))  derive  not(w ~ 0).
(defn- nn-distinct-from-zero [w h]
  (function/lam [['z (nn-equiv w nnzero)]]
                (app (nn-pright (nn-le nnzero w) (pneg (nn-equiv nnzero w)) h)
                     (nn-esym w nnzero 'z))))

(def square-strict-convex-spec
  {:name 'signed/square-strict-convex
   :universes []
   :type (app (function/const* 'signed/strict-convex-on []) wsum-fn)
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
     ['hw0 (nn-lt nnzero 'w0)] ['hw1 (nn-lt nnzero 'w1)]
     ['hw (nn-equiv (radd 'w0 'w1) rone)] ['hxy (pneg (seqv 'x 'y))]]
    (let [W0 (fnn 'w0) W1 (fnn 'w1)
          comb (sadd (smul W0 'x) (smul W1 'y))
          csq (smul comb comb)
          dxy (ssub 'x 'y) dd (smul dxy dxy)
          W01 (smul W0 W1) var (smul W01 dd)
          rhs (sadd (smul W0 (smul 'x 'x)) (smul W1 (smul 'y 'y)))
          variance (variance-id 'w0 'w1 'x 'y 'hw)              ; csq + var ~ rhs
          le (square-cvx 'w0 'w1 'x 'y 'hw)                     ; csq <= rhs
          W0nz (from-nn-nonzero 'w0 (nn-distinct-from-zero 'w0 'hw0))   ; W0 !~ 0
          W1nz (from-nn-nonzero 'w1 (nn-distinct-from-zero 'w1 'hw1))   ; W1 !~ 0
          W01nz (mult-nonzero W0 W1 W0nz W1nz)                  ; W0*W1 !~ 0
          dxynz (function/lam [['h (seqv dxy szero)]]           ; (x-y) !~ 0
                              (app 'hxy (sub-reflect 'x 'y 'h)))
          ddnz (sq-nonzero dxy dxynz)                           ; (x-y)^2 !~ 0
          varnz (mult-nonzero W01 dd W01nz ddnz)                ; var !~ 0
          neq (function/lam
               [['h (seqv csq rhs)]]
               (let [e1 (etr (sadd csq var) rhs csq variance (esym csq rhs 'h))    ; csq+var ~ csq
                     e2 (etr (sadd csq var) csq (sadd csq szero)
                             e1 (esym (sadd csq szero) csq (addzr csq)))           ; csq+var ~ csq+0
                     varz (add-left-cancel var szero csq e2)]                       ; var ~ 0
                 (app varnz varz)))]
      (lt-intro csq rhs le neq)))})

(def theorem-specs [from-nnrat-nonzero-spec strict-convex-on-spec square-strict-convex-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.square-convex rainbow.math.rational.signed.square-nonzero rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.nnrat.strict-order rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.math.linear.matrix.least-squares-equality])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-strict-convex theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-strict-convex))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
