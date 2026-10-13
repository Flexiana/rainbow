(ns rainbow.math.rational.nnrat.farkas-partition-covered
  "The vacuity FIX for the partition keystone:
  farkas-partition-list-necessary strengthened with a COVERING conjunct that
  ties the output partition to the input, killing the empty witness.

  farkas-partition-list-necessary concludes EXISTS (lower,upper), lowers-sat /\\
  uppers-sat -- which the EMPTY pair satisfies (a fold over nil is truth), so it
  is vacuous. The partition is proof-dependent (partition-row classifies each
  row by use-disjunction), so an explicit-output rewrite is unavailable; the fix
  keeps the existential and adds

    length(lower) + length(upper) = length(rows)

  which the empty pair fails for non-empty rows (0 =/= length(rows)). This module
  proves the strengthened theorem nnrat/farkas-partition-list-covered by the same
  List.rec as the original, additionally threading the length equation: nil is
  reflexivity (0+0 = 0), the lower cons is one succ-congruence (both sides reduce
  to succ(..) definitionally), the upper cons is a short transitive chain via
  nat/add-commutative (a + succ b is not definitional; succ b + a is). Built as a
  NEW theorem so the existing consumers are not disturbed; migrating them is a
  follow-on. The covering conjunct's non-vacuity is independently checked in
  nnrat_farkas_partition_covering_design_test. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-partition-row :as prow]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as upper]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list-lower :as lower]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def p2 (product nnrat nnrat))
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def pair-lists (product list-a list-a))
(def nat (function/const* 'data/Nat []))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- nil-of [c] (function/app (function/const* 'data/nil [type-level]) c))
(defn- cons-of [c h t] (function/app (function/const* 'data/cons [type-level]) c h t))

(defn- bs-a [r] (fst nnrat bpq r))
(defn- bs-b [r] (fst nnrat p2 (snd nnrat bpq r)))
(defn- bs-p [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat bpq r))))
(defn- bs-q [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat bpq r))))

(defn- reduced-conditions [rows w]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows w))
(defn- row-reduced [r w]
  (proposition/disjunction
   (function/app (function/const* 'proposition/existence [type-level]) nnrat
                 (function/lam [['d nnrat]]
                               (proposition/conjunction
                                (equiv (add (bs-a r) 'd) (bs-b r))
                                (at-most (bs-p r) (add (mul 'd w) (bs-q r))))))
   (function/app (function/const* 'proposition/existence [type-level]) nnrat
                 (function/lam [['d nnrat]]
                               (proposition/conjunction
                                (equiv (add (bs-b r) 'd) (bs-a r))
                                (at-most (add (mul 'd w) (bs-p r)) (bs-q r)))))))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- partition-row [a b p q w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-row []) a b p q w reduced))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- disjunction [l r] (function/app (function/const* 'proposition/disjunction []) l r))
(defn- use-disjunction [l r result e onl onr]
  (function/app (function/const* 'proposition/use-disjunction []) l r result e onl onr))
(defn- existence [pred]
  (function/app (function/const* 'proposition/existence [type-level]) pair-lists pred))
(defn- witness [pred value evidence]
  (function/app (function/const* 'proposition/witness [type-level]) pair-lists pred value evidence))
(defn- use-witness [pred result evidence cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) pair-lists pred result evidence cont))
(defn- existence-nn [pred]
  (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- use-witness-nn [pred result evidence cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) nnrat pred result evidence cont))

(defn- lower-row [d q p] (pair nnrat p2 d (pair nnrat nnrat q p)))
(defn- upper-row [d p q] (pair nnrat p2 d (pair nnrat nnrat p q)))
(defn- lower-holds [p d w q] (at-most p (add (mul d w) q)))
(defn- upper-holds [d w p q] (at-most (add (mul d w) p) q))
(def trivial (function/const* 'proposition/trivial []))

;; length / nat-equation machinery
(defn- len-a [l] (function/app (function/const* 'list/length [type-level]) arow l))
(defn- len-bs [l] (function/app (function/const* 'list/length [type-level]) bs-row l))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- neq [a b] (function/equality type-level nat a b))
(def nat-zero (function/const* 'data/zero []))
(defn- refl-nat [a] (function/app (function/const* 'equality/reflexive [type-level]) nat a))
(def succ-fn (function/lam [['n nat]] (function/app (function/const* 'data/succ []) 'n)))
(defn- congr-succ [a b h]                       ; a=b -> succ a = succ b
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat succ-fn a b h))
(defn- eq-trans [x y z hxy hyz]
  (function/app (function/const* 'equality/transitive [type-level]) nat x y z hxy hyz))
(defn- add-comm [a b] (function/app (function/const* 'nat/add-commutative []) a b))

;; the covering length equation for a candidate pair pr over rows rs
(defn- len-eq [pr rs]
  (neq (nadd (len-a (fst list-a list-a pr)) (len-a (snd list-a list-a pr))) (len-bs rs)))
;; the strengthened goal predicate / goal
(defn- goal-pred [rs w]
  (function/lam
   [['pr pair-lists]]
   (conjunction (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                             (uppers-sat (snd list-a list-a 'pr) w))
                (len-eq 'pr rs))))
(defn- goal [rs w] (existence (goal-pred rs w)))

(def partition-covered-spec
  {:name 'nnrat/farkas-partition-list-covered
   :universes []
   :type
   (function/forall
    [['rows list-bs] ['w nnrat] ['reduced (reduced-conditions 'rows 'w)]]
    (goal 'rows 'w))
   :value
   (function/lam
    [['rows list-bs] ['w nnrat] ['reduced (reduced-conditions 'rows 'w)]]
    (let [motive (function/lam
                  [['rs list-bs]]
                  (function/arrow (reduced-conditions 'rs 'w) (goal 'rs 'w)))
          ;; nil: (nil,nil); lengths 0+0 = 0 = length nil, so reflexivity
          nil-case
          (function/lam
           [['hnil (reduced-conditions (nil-of bs-row) 'w)]]
           (let [nl (nil-of arow)]
             (witness (goal-pred (nil-of bs-row) 'w) (pair list-a list-a nl nl)
                      (conjoin (conjunction (lowers-sat nl 'w) (uppers-sat nl 'w))
                               (len-eq (pair list-a list-a nl nl) (nil-of bs-row))
                               (conjoin (lowers-sat nl 'w) (uppers-sat nl 'w) trivial trivial)
                               (refl-nat nat-zero)))))
          cons-case
          (function/lam
           [['head bs-row] ['tail list-bs]
            ['ih (function/arrow (reduced-conditions 'tail 'w) (goal 'tail 'w))]]
           (function/lam
            [['hcons (reduced-conditions (cons-of bs-row 'head 'tail) 'w)]]
            (let [rr (row-reduced 'head 'w)
                  rest (reduced-conditions 'tail 'w)
                  r-red (left-conjunct rr rest 'hcons)
                  tail-red (right-conjunct rr rest 'hcons)
                  ih-goal (function/app 'ih tail-red)
                  cons-rows (cons-of bs-row 'head 'tail)
                  lo-out (existence-nn (function/lam [['d nnrat]]
                                                     (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))))
                  up-out (existence-nn (function/lam [['d nnrat]]
                                                     (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))))
                  part (partition-row (bs-a 'head) (bs-b 'head) (bs-p 'head) (bs-q 'head) 'w r-red)]
              (use-witness
               (goal-pred 'tail 'w) (goal cons-rows 'w) ih-goal
               (function/lam
                [['pr pair-lists]
                 ['pr-proof (function/app (goal-pred 'tail 'w) 'pr)]]
                (let [l0 (fst list-a list-a 'pr)
                      u0 (snd list-a list-a 'pr)
                      sat-conj (conjunction (lowers-sat l0 'w) (uppers-sat u0 'w))
                      lenq (len-eq 'pr 'tail)
                      sat-conj0 (left-conjunct sat-conj lenq 'pr-proof)
                      length-eq0 (right-conjunct sat-conj lenq 'pr-proof)
                      lo-sat0 (left-conjunct (lowers-sat l0 'w) (uppers-sat u0 'w) sat-conj0)
                      up-sat0 (right-conjunct (lowers-sat l0 'w) (uppers-sat u0 'w) sat-conj0)
                      len-l0 (len-a l0) len-u0 (len-a u0)]
                  (use-disjunction
                   lo-out up-out (goal cons-rows 'w) part
                   ;; lower: new-l = cons row l0; length via one succ-congruence
                   (function/lam
                    [['lo lo-out]]
                    (use-witness-nn
                     (function/lam [['d nnrat]]
                                   (lower-holds (bs-p 'head) 'd 'w (bs-q 'head)))
                     (goal cons-rows 'w) 'lo
                     (function/lam
                      [['d nnrat]
                       ['dh (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))]]
                      (let [new-l (cons-of arow (lower-row 'd (bs-q 'head) (bs-p 'head)) l0)]
                        (witness (goal-pred cons-rows 'w) (pair list-a list-a new-l u0)
                                 (conjoin (conjunction (lowers-sat new-l 'w) (uppers-sat u0 'w))
                                          (len-eq (pair list-a list-a new-l u0) cons-rows)
                                          (conjoin (lowers-sat new-l 'w) (uppers-sat u0 'w)
                                                   (conjoin (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))
                                                            (lowers-sat l0 'w) 'dh lo-sat0)
                                                   up-sat0)
                                          (congr-succ (nadd len-l0 len-u0) (len-bs 'tail) length-eq0)))))))
                   ;; upper: new-u = cons row u0; length via commute + transitive
                   (function/lam
                    [['up up-out]]
                    (use-witness-nn
                     (function/lam [['d nnrat]]
                                   (upper-holds 'd 'w (bs-p 'head) (bs-q 'head)))
                     (goal cons-rows 'w) 'up
                     (function/lam
                      [['d nnrat]
                       ['dh (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))]]
                      (let [new-u (cons-of arow (upper-row 'd (bs-p 'head) (bs-q 'head)) u0)
                            t1 (add-comm len-l0 (function/app (function/const* 'data/succ []) len-u0))
                            t2 (congr-succ (nadd len-u0 len-l0) (nadd len-l0 len-u0)
                                           (add-comm len-u0 len-l0))
                            t3 (congr-succ (nadd len-l0 len-u0) (len-bs 'tail) length-eq0)
                            succ (fn [x] (function/app (function/const* 'data/succ []) x))
                            inner (eq-trans (succ (nadd len-u0 len-l0))
                                            (succ (nadd len-l0 len-u0))
                                            (succ (len-bs 'tail)) t2 t3)
                            len-proof (eq-trans (nadd len-l0 (succ len-u0))
                                                (nadd (succ len-u0) len-l0)
                                                (succ (len-bs 'tail)) t1 inner)]
                        (witness (goal-pred cons-rows 'w) (pair list-a list-a l0 new-u)
                                 (conjoin (conjunction (lowers-sat l0 'w) (uppers-sat new-u 'w))
                                          (len-eq (pair list-a list-a l0 new-u) cons-rows)
                                          (conjoin (lowers-sat l0 'w) (uppers-sat new-u 'w)
                                                   lo-sat0
                                                   (conjoin (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))
                                                            (uppers-sat u0 'w) 'dh up-sat0))
                                          len-proof)))))))))))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        bs-row motive nil-case cons-case 'rows)
       'reduced)))})

(def definition-specs [])
(def theorem-specs [partition-covered-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-partition-row rainbow.math.rational.nnrat.farkas-reduce-list rainbow.math.rational.nnrat.farkas-elim-affine-list rainbow.math.rational.nnrat.farkas-elim-affine-list-lower])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-partition-covered (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-partition-covered))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
