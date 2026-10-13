(ns rainbow.math.rational.nnrat.farkas-partition-row
  "Piece (ii) brick 1 core: the per-row
  step of the dependent partition.

  One elimination round's output, reduced-conditions, is a fold of
  disjunctions: each reduced row is
    (EXISTS D, A+D~B /\\ P<=D*v+Q)  OR  (EXISTS D, B+D~A /\\ D*v+P<=Q).
  To thread that into the next round it must become a lower-row list and an
  upper-row list. This is the per-row core: a reduced row becomes an affine
  LOWER constraint (EXISTS D, P<=D*v+Q) or an affine UPPER constraint
  (EXISTS D, D*v+P<=Q) -- dropping the difference-witness conjunct
  (A+D~B / B+D~A), which the next round does not need; it only needs the
  affine constraint itself. nnrat/farkas-partition-row proves the reduced
  disjunction implies this stripped disjunction, by use-disjunction +
  use-witness + right-conjunct + re-witness. The list accumulation building
  the two lists from this per-row step is brick 1 proper. Native proof data,
  axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def type-level [:succ [:zero]])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- disjunction [l r]
  (function/app (function/const* 'proposition/disjunction []) l r))
(defn- left-disjunct [l r e]
  (function/app (function/const* 'proposition/left-disjunct []) l r e))
(defn- right-disjunct [l r e]
  (function/app (function/const* 'proposition/right-disjunct []) l r e))
(defn- use-disjunction [l r result e on-l on-r]
  (function/app (function/const* 'proposition/use-disjunction [])
                l r result e on-l on-r))
(defn- existence [pred]
  (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- witness [pred value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat pred value evidence))
(defn- use-witness [pred result evidence cont]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nnrat pred result evidence cont))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))

(def partition-row-spec
  {:name 'nnrat/farkas-partition-row
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['reduced
      (disjunction
       (existence (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'a 'd) 'b)
                                (at-most 'p (add (mul 'd 'v) 'q)))))
       (existence (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'b 'd) 'a)
                                (at-most (add (mul 'd 'v) 'p) 'q)))))]]
    (disjunction
     (existence (function/lam [['d nnrat]] (at-most 'p (add (mul 'd 'v) 'q))))
     (existence (function/lam [['d nnrat]] (at-most (add (mul 'd 'v) 'p) 'q)))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['reduced
      (disjunction
       (existence (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'a 'd) 'b)
                                (at-most 'p (add (mul 'd 'v) 'q)))))
       (existence (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'b 'd) 'a)
                                (at-most (add (mul 'd 'v) 'p) 'q)))))]]
    (let [lo-pred (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'a 'd) 'b)
                                (at-most 'p (add (mul 'd 'v) 'q))))
          up-pred (function/lam
                   [['d nnrat]]
                   (conjunction (equiv (add 'b 'd) 'a)
                                (at-most (add (mul 'd 'v) 'p) 'q)))
          lo-ex (existence lo-pred)
          up-ex (existence up-pred)
          out-lo-pred (function/lam
                       [['d nnrat]] (at-most 'p (add (mul 'd 'v) 'q)))
          out-up-pred (function/lam
                       [['d nnrat]] (at-most (add (mul 'd 'v) 'p) 'q))
          out-lo (existence out-lo-pred)
          out-up (existence out-up-pred)
          result (disjunction out-lo out-up)]
      (use-disjunction
       lo-ex up-ex result 'reduced
       ;; left: reduced row is a lower row -> keep the affine lower constraint
       (function/lam
        [['lower lo-ex]]
        (use-witness
         lo-pred result 'lower
         (function/lam
          [['d nnrat]
           ['conj (conjunction (equiv (add 'a 'd) 'b)
                               (at-most 'p (add (mul 'd 'v) 'q)))]]
          (left-disjunct
           out-lo out-up
           (witness out-lo-pred 'd
                    (right-conjunct (equiv (add 'a 'd) 'b)
                                    (at-most 'p (add (mul 'd 'v) 'q))
                                    'conj))))))
       ;; right: reduced row is an upper row -> keep the affine upper constraint
       (function/lam
        [['upper up-ex]]
        (use-witness
         up-pred result 'upper
         (function/lam
          [['d nnrat]
           ['conj (conjunction (equiv (add 'b 'd) 'a)
                               (at-most (add (mul 'd 'v) 'p) 'q))]]
          (right-disjunct
           out-lo out-up
           (witness out-up-pred 'd
                    (right-conjunct (equiv (add 'b 'd) 'a)
                                    (at-most (add (mul 'd 'v) 'p) 'q)
                                    'conj)))))))))})

(def definition-specs [])
(def theorem-specs [partition-row-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-farkas-partition-row
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
