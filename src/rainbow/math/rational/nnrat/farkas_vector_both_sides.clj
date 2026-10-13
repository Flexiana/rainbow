(ns rainbow.math.rational.nnrat.farkas-vector-both-sides
  "The unified representation, second-variable step:
  convert a reduced both-sides COEFFICIENT-VECTOR row into a lower/upper
  affine row in the next variable x2, subtraction-free.

  One round (nnrat/farkas-cross-vectors / -all-reduced) eliminates x1 and
  leaves, per (lower,upper) pair, the reduced both-sides vector constraint

    b_L*u1 + eval(scale l1 u-tail)  <=  b_U*l1 + eval(scale u1 l-tail).

  When the tails are headed by the NEXT variable x2 -- u-tail = (a2u,x2)::ru,
  l-tail = (a2l,x2)::rl -- both scaled evals reduce definitionally
  (farkas-scale-right's cons case, then linear-form's cons case) to
  A*x2 + rest, so the whole constraint is affine in x2 on both sides:

    CL + (AL*x2 + EL)  <=  CR + (AR*x2 + ER)

  with AL = a2u*l1, AR = a2l*u1, CL = b_L*u1, CR = b_U*l1,
  EL = eval(scale l1 ru), ER = eval(scale u1 rl). Grouping the x2 term to the
  front (commute/reassociate, no subtraction) gives exactly the shape
  nnrat/farkas-both-sides-to-lower / -to-upper consume, so with the
  difference witness (AL+D~AR for a lower row, AR+D~AL for an upper row) this
  produces the reduced constraint for eliminating x2:

    to-lower:  (CL + EL)          <=  D*x2 + (CR + ER)       -- x2 lower-bounded
    to-upper:  D*x2 + (CL + EL)   <=  (CR + ER)              -- x2 upper-bounded

  These are the both-sides rows the next round crosses (packaging CL+EL /
  CR+ER as coefficient vectors with a unit column is the follow-on brick).
  This is the vector-level analogue of nnrat/farkas-both-sides, and the
  per-row core of the coefficient-vector partition that closes the
  over-variable recursion's step. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-both-sides :as both-sides]
            [rainbow.math.rational.nnrat.farkas-form-scale :as form-scale]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nn
  (function/app (function/const* 'data/Product [type-level type-level]) nnrat nnrat))
(def list-pair
  (function/app (function/const* 'data/List [type-level]) pair-nn))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
(defn- pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))

(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- etrans [l m r a b]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r a b))
(defn- esym [l r same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- add-associative [a b c]
  (function/app (function/const* 'nnrat/add-associative []) a b c))
(defn- add-commutative [a b]
  (function/app (function/const* 'nnrat/add-commutative []) a b))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- at-most-respects [l el r er sl sr ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                l el r er sl sr ordered))
(defn- to-lower [a b d p q v diff bs]
  (function/app (function/const* 'nnrat/farkas-both-sides-to-lower [])
                a b d p q v diff bs))
(defn- to-upper [a b d p q v diff bs]
  (function/app (function/const* 'nnrat/farkas-both-sides-to-upper [])
                a b d p q v diff bs))

;; group-front: add C (add M E) ~ add M (add C E)  (commute/reassociate, no subtraction)
(defn- group-front [c m e]
  (etrans (add m (add c e)) (add (add c m) e) (add c (add m e))
          (etrans (add m (add c e)) (add (add m c) e) (add (add c m) e)
                  (esym (add (add m c) e) (add m (add c e))
                        (add-associative m c e))
                  (add-respects (add m c) (add c m) e e
                                (add-commutative m c) (erefl e)))
          (add-associative c m e)))

;; the reduced both-sides vector row, as nnrat/farkas-cross-vectors produces
;; it, with tails headed by the next variable x2.
(defn- reduced-row [b-l u-coeff l-coeff u-tail b-u l-tail]
  (at-most (add (mul b-l u-coeff) (eval-form (scale-right l-coeff u-tail)))
           (add (mul b-u l-coeff) (eval-form (scale-right u-coeff l-tail)))))

;; common parameter list
(def params
  [['l-coeff nnrat] ['u-coeff nnrat] ['b-l nnrat] ['b-u nnrat]
   ['a2l nnrat] ['a2u nnrat] ['rl list-pair] ['ru list-pair]
   ['x2 nnrat] ['d nnrat]])

(defn- al [] (mul 'a2u 'l-coeff))                 ; x2 coeff on the LEFT
(defn- ar [] (mul 'a2l 'u-coeff))                 ; x2 coeff on the RIGHT
(defn- cl [] (mul 'b-l 'u-coeff))
(defn- cr [] (mul 'b-u 'l-coeff))
(defn- el [] (eval-form (scale-right 'l-coeff 'ru)))
(defn- er [] (eval-form (scale-right 'u-coeff 'rl)))
(def u-tail-full (cons-pair (pair 'a2u 'x2) 'ru))
(def l-tail-full (cons-pair (pair 'a2l 'x2) 'rl))

;; the input row (stated in the exact cross-vectors output form; defeq to the
;; affine-in-x2 grouping the proof works with)
(defn- input-row []
  (reduced-row 'b-l 'u-coeff 'l-coeff u-tail-full 'b-u l-tail-full))

;; the transported hypothesis with the x2 term grouped to the front on each
;; side: (AL*x2 + (CL+EL)) <= (AR*x2 + (CR+ER)). Reused by both directions.
;; at-most-respects takes (new-left old-left new-right old-right sameL sameR
;; ordered) with sameL : new-left ~ old-left; group-front gives exactly that
;; (grouped ~ original), transporting the input row 'h to the grouped form.
(defn- grouped-hyp []
  (let [ml (mul (al) 'x2)
        mr (mul (ar) 'x2)]
    (at-most-respects
     (add ml (add (cl) (el)))            ; new-left  (grouped, x2 coeff up front)
     (add (cl) (add ml (el)))            ; old-left  (defeq to input LHS)
     (add mr (add (cr) (er)))            ; new-right (grouped)
     (add (cr) (add mr (er)))            ; old-right (defeq to input RHS)
     (group-front (cl) ml (el))          ; new-left ~ old-left
     (group-front (cr) mr (er))          ; new-right ~ old-right
     'h)))

(def vector-both-sides-to-lower-spec
  {:name 'nnrat/farkas-vector-both-sides-to-lower
   :universes []
   :type
   (function/forall
    (conj params
          ['diff (equiv (add (al) 'd) (ar))]
          ['h (input-row)])
    (at-most (add (cl) (el)) (add (mul 'd 'x2) (add (cr) (er)))))
   :value
   (function/lam
    (conj params
          ['diff (equiv (add (al) 'd) (ar))]
          ['h (input-row)])
    (to-lower (al) (ar) 'd (add (cl) (el)) (add (cr) (er)) 'x2 'diff
              (grouped-hyp)))})

(def vector-both-sides-to-upper-spec
  {:name 'nnrat/farkas-vector-both-sides-to-upper
   :universes []
   :type
   (function/forall
    (conj params
          ['diff (equiv (add (ar) 'd) (al))]
          ['h (input-row)])
    (at-most (add (mul 'd 'x2) (add (cl) (el))) (add (cr) (er))))
   :value
   (function/lam
    (conj params
          ['diff (equiv (add (ar) 'd) (al))]
          ['h (input-row)])
    (to-upper (al) (ar) 'd (add (cl) (el)) (add (cr) (er)) 'x2 'diff
              (grouped-hyp)))})

(def definition-specs [])
(def theorem-specs [vector-both-sides-to-lower-spec vector-both-sides-to-upper-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-both-sides rainbow.math.rational.nnrat.farkas-form-scale])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-both-sides (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-both-sides))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
