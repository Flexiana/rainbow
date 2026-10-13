(ns rainbow.math.rational.nnrat.farkas-vector-partition-pack
  "The unified representation, partition bridge (single row)
 : pack one reduced coefficient-vector
  row into a both-sides DATA row and discharge its reduced-conditions entry.

  Architectural finding (2026-09-09): the affine
  nnrat/farkas-partition-list-necessary is generic in the per-row (A,B,P,Q).
  It consumes a data list of both-sides rows (A,(B,(P,Q))) plus a proof that
  nnrat/farkas-reduced-conditions holds (the per-row lower/upper disjunction
  fold), and returns the next round's lower/upper AFFINE-row lists. So the
  coefficient-vector round needs only a BRIDGE that packs its reduced rows as
  that data and supplies that proof -- no re-proved partition.

  This is the bridge's single-row core. A reduced both-sides vector row
  (farkas-cross-vectors output, tails headed by the next variable x2) packs
  into the data row (AL,(AR,(P,Q))) with AL = a2u*l1, AR = a2l*u1,
  P = b_L*u1 + eval(scale l1 ru), Q = b_U*l1 + eval(scale u1 rl). For that
  packed row the projections bs-a/bs-b/bs-p/bs-q reduce definitionally to
  AL/AR/P/Q, so reduce-list's per-row disjunction (row-reduced) is defeq to
  nnrat/farkas-vector-both-sides-reduce's output. Hence
  farkas-reduced-conditions of the one-element packed list is just that
  reduction conjoined with truth. nnrat/farkas-vector-partition-pack proves
  it -- the defeq-carry that lets the bilist fold (the bridge proper) emit a
  list-bs of packed rows and its reduced-conditions proof, then hand them to
  the already-proved partition. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce :as vbsr]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def list-pair (function/app (function/const* 'data/List [type-level]) pair-nn))
;; reduce-list's both-sides row shape: (A,(B,(P,Q)))
(def pq pair-nn)
(def bpq (product nnrat pq))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))

(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- pair-nnnn [x y] (pair2 nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- cons-bs [h t] (function/app (function/const* 'data/cons [type-level]) bs-row h t))
(def nil-bs (function/app (function/const* 'data/nil [type-level]) bs-row))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- reduced-conditions [rows v]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows v))
(defn- vec-reduce [lc uc bl bu a2l a2u rl ru x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-both-sides-reduce [])
                lc uc bl bu a2l a2u rl ru x2 h))

(def params
  [['l-coeff nnrat] ['u-coeff nnrat] ['b-l nnrat] ['b-u nnrat]
   ['a2l nnrat] ['a2u nnrat] ['rl list-pair] ['ru list-pair] ['x2 nnrat]])

(defn- al [] (mul 'a2u 'l-coeff))
(defn- ar [] (mul 'a2l 'u-coeff))
(defn- pp [] (add (mul 'b-l 'u-coeff) (eval-form (scale-right 'l-coeff 'ru))))   ; CL+EL
(defn- qq [] (add (mul 'b-u 'l-coeff) (eval-form (scale-right 'u-coeff 'rl))))   ; CR+ER
(def u-tail-full (cons-pair (pair-nnnn 'a2u 'x2) 'ru))
(def l-tail-full (cons-pair (pair-nnnn 'a2l 'x2) 'rl))

;; the packed both-sides data row (AL,(AR,(P,Q)))
(defn- packed []
  (pair2 nnrat bpq (al)
         (pair2 nnrat pq (ar) (pair-nnnn (pp) (qq)))))

;; the reduced vector row, as farkas-cross-vectors produces it
(defn- input-row []
  (function/app
   (function/app (function/const* 'nnrat/at-most [])
                 (add (mul 'b-l 'u-coeff) (eval-form (scale-right 'l-coeff u-tail-full))))
   (add (mul 'b-u 'l-coeff) (eval-form (scale-right 'u-coeff l-tail-full)))))

;; farkas-vector-both-sides-reduce's output proposition (defeq to
;; row-reduced (packed) x2), spelled out so conjoin's L argument is explicit.
(defn- reduced-disjunction []
  (let [equiv (fn [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
        at-most (fn [a b] (function/app (function/const* 'nnrat/at-most []) a b))
        conj (fn [a b] (function/app (function/const* 'proposition/conjunction []) a b))
        exists (fn [pred] (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
        disj (fn [a b] (function/app (function/const* 'proposition/disjunction []) a b))]
    (disj
     (exists (function/lam [['d nnrat]]
                           (conj (equiv (add (al) 'd) (ar))
                                 (at-most (pp) (add (mul 'd 'x2) (qq))))))
     (exists (function/lam [['d nnrat]]
                           (conj (equiv (add (ar) 'd) (al))
                                 (at-most (add (mul 'd 'x2) (pp)) (qq))))))))

(def partition-pack-spec
  {:name 'nnrat/farkas-vector-partition-pack
   :universes []
   :type
   (function/forall
    (conj params ['h (input-row)])
    (reduced-conditions (cons-bs (packed) nil-bs) 'x2))
   :value
   (function/lam
    (conj params ['h (input-row)])
    ;; reduced-conditions (cons packed nil) x2 reduces to
    ;; conjunction (row-reduced packed x2) truth; row-reduced packed x2 is
    ;; defeq to the reduction below (projections), truth is trivial.
    (conjoin (reduced-disjunction) (proposition/truth)
             (vec-reduce 'l-coeff 'u-coeff 'b-l 'b-u 'a2l 'a2u 'rl 'ru 'x2 'h)
             (function/const* 'proposition/trivial [])))})

(def definition-specs [])
(def theorem-specs [partition-pack-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce rainbow.math.rational.nnrat.farkas-reduce-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-partition-pack (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-partition-pack))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
