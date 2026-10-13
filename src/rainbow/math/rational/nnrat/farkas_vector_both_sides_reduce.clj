(ns rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce
  "The unified representation, per-row reduction:
  reduce a both-sides COEFFICIENT-VECTOR row to a lower/upper affine row in
  the next variable x2 -- as a disjunction, ready for the partition.

  A reduced both-sides vector row (nnrat/farkas-cross-vectors output) with
  tails headed by x2 is affine in x2 on both sides:
  CL + (AL*x2 + EL) <= CR + (AR*x2 + ER), with AL = a2u*l1, AR = a2l*u1,
  CL = b_L*u1, CR = b_U*l1, EL = eval(scale l1 ru), ER = eval(scale u1 rl).
  Grouping the x2 term to the front (commute/reassociate, no subtraction)
  matches the shape nnrat/farkas-both-sides-reduce consumes, so this row
  reduces exactly as the affine both-sides row does:

    -> (EXISTS D, AL+D~AR /\\ (CL+EL) <= D*x2+(CR+ER))
       OR (EXISTS D, AR+D~AL /\\ D*x2+(CL+EL) <= (CR+ER))

  a LOWER row in x2 when AL<=AR, an UPPER row when AR<=AL. The whole
  reduction reuses the proved nnrat/farkas-both-sides-reduce (order-totality,
  the difference witness, the both-sides conversions) after the grouping --
  no new arithmetic. This is the vector-level analogue of
  nnrat/farkas-both-sides-reduce and the per-row core of the coefficient-
  vector partition: mapping it over the reduced-row list, then stripping the
  disjunction (nnrat/farkas-partition-row / -list) into a lower-list and an
  upper-list, is the concrete step the over-variable recursion folds. Native
  proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-both-sides-reduce :as reduce]
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
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- disjunction [l r]
  (function/app (function/const* 'proposition/disjunction []) l r))
(defn- existence [pred]
  (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
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
(defn- both-sides-reduce [a b p q v both]
  (function/app (function/const* 'nnrat/farkas-both-sides-reduce [])
                a b p q v both))

;; group-front: add M (add C E) ~ add C (add M E)  (grouped ~ original)
(defn- group-front [c m e]
  (etrans (add m (add c e)) (add (add c m) e) (add c (add m e))
          (etrans (add m (add c e)) (add (add m c) e) (add (add c m) e)
                  (esym (add (add m c) e) (add m (add c e)) (add-associative m c e))
                  (add-respects (add m c) (add c m) e e (add-commutative m c) (erefl e)))
          (add-associative c m e)))

(def params
  [['l-coeff nnrat] ['u-coeff nnrat] ['b-l nnrat] ['b-u nnrat]
   ['a2l nnrat] ['a2u nnrat] ['rl list-pair] ['ru list-pair] ['x2 nnrat]])

(defn- al [] (mul 'a2u 'l-coeff))
(defn- ar [] (mul 'a2l 'u-coeff))
(defn- cl [] (mul 'b-l 'u-coeff))
(defn- cr [] (mul 'b-u 'l-coeff))
(defn- el [] (eval-form (scale-right 'l-coeff 'ru)))
(defn- er [] (eval-form (scale-right 'u-coeff 'rl)))
(def u-tail-full (cons-pair (pair 'a2u 'x2) 'ru))
(def l-tail-full (cons-pair (pair 'a2l 'x2) 'rl))

(defn- input-row []
  (at-most (add (cl) (eval-form (scale-right 'l-coeff u-tail-full)))
           (add (cr) (eval-form (scale-right 'u-coeff l-tail-full)))))

;; transport the input row to the grouped affine-in-x2 both-sides shape
;; farkas-both-sides-reduce consumes: (AL*x2 + (CL+EL)) <= (AR*x2 + (CR+ER)).
(defn- grouped-hyp []
  (let [ml (mul (al) 'x2)
        mr (mul (ar) 'x2)]
    (at-most-respects
     (add ml (add (cl) (el)))            ; new-left  (grouped)
     (add (cl) (add ml (el)))            ; old-left  (defeq input LHS)
     (add mr (add (cr) (er)))            ; new-right
     (add (cr) (add mr (er)))            ; old-right (defeq input RHS)
     (group-front (cl) ml (el))          ; new-left ~ old-left
     (group-front (cr) mr (er))          ; new-right ~ old-right
     'h)))

;; the reduced disjunction, in exactly farkas-partition-row's input shape
;; (A = AL, B = AR, P = CL+EL, Q = CR+ER, v = x2).
(defn- reduced-disjunction []
  (disjunction
   (existence (function/lam
               [['d nnrat]]
               (conjunction (equiv (add (al) 'd) (ar))
                            (at-most (add (cl) (el))
                                     (add (mul 'd 'x2) (add (cr) (er)))))))
   (existence (function/lam
               [['d nnrat]]
               (conjunction (equiv (add (ar) 'd) (al))
                            (at-most (add (mul 'd 'x2) (add (cl) (el)))
                                     (add (cr) (er))))))))

(def vector-both-sides-reduce-spec
  {:name 'nnrat/farkas-vector-both-sides-reduce
   :universes []
   :type
   (function/forall
    (conj params ['h (input-row)])
    (reduced-disjunction))
   :value
   (function/lam
    (conj params ['h (input-row)])
    (both-sides-reduce (al) (ar) (add (cl) (el)) (add (cr) (er)) 'x2
                       (grouped-hyp)))})

(def definition-specs [])
(def theorem-specs [vector-both-sides-reduce-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      reduce/extend-environment
      form-scale/extend-environment
      (support/extend-with :nnrat-farkas-vector-both-sides-reduce
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
