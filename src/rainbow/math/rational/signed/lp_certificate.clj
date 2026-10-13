(ns rainbow.math.rational.signed.lp-certificate
  "A worked LP optimality certificate on concrete numbers, including a NEGATIVE
  cost -- the per-instance end of the verified-optimization pipeline.

  The program is a two-product mix where the second product carries a penalty
  rather than a margin:

      maximize   2*x0 - 1*x1
      subject to x0 + x1 <= 4        (shared capacity)
                 x0      <= 3        (a line limit)
                 x >= 0

  The proposed decision is x = (3, 0) and the proposed dual price vector is
  y = (0, 2): capacity is not binding so it prices at zero, the line limit is
  binding so it carries the whole margin. Both objectives evaluate to 6, so the
  duality gap is closed and the pair is a certificate.

  What the kernel then checks is
  `optimization/signed-lp-worked-optimal` : no feasible plan scores above 6.

  Two things make this the shape a buyer can use.

  First, the cost -1 is not expressible in the nnrat LP stack at all, so this
  instance is only checkable through the signed theorems. Real programs have
  penalties, and a checker that cannot represent them checks nothing that
  matters.

  Second, EVERY hypothesis is discharged by computation. Feasibility, dual
  feasibility and nonnegativity are each `signed/decide-at-most-true-sound`
  applied to a reflexivity witness: the comparison reduces, reflexivity records
  that it reduced to `true`, soundness converts it. No inequality here was proved
  by hand. That is what makes the pattern cheap enough to run per instance while
  the expensive theorem -- `optimization/signed-lp-optimality-certificate`,
  proved once for every matrix, cost vector and dual vector -- is reused
  unchanged.

  Native and axiom-free on D63; chains the signed LP duality theorems and the
  decidable signed order."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.lp-duality :as lp]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def bool-false (function/const* 'data/false []))
(def bool-true (function/const* 'data/true []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [zero-level]) A f xs))

;; ---- concrete data ---------------------------------------------------------

(defn- numeral [n]
  (if (zero? n)
    (function/const* 'data/zero [])
    (app (function/const* 'data/succ []) (numeral (dec n)))))

(defn- whole [n]
  (app (function/const* 'nnrat/make []) (numeral n) (function/const* 'data/zero [])))

(defn- money
  "A signed literal as a Grothendieck pair: `money p n` is p - n."
  [p n]
  (app (function/const* 'signed/make []) (whole p) (whole n)))

;; Bool.rec at the value level: a two-element vector as a function
(defn- pick [at-false at-true]
  (function/lam
   [['index bool]]
   (app (function/const* 'data/Bool.rec [type-level])
        (function/lam [['ignored bool]] signed)
        at-false at-true 'index)))

;; a two-element index list, in the order the sums fold over
(def index-list
  (app (function/const* 'data/cons [type-level]) bool bool-false
       (app (function/const* 'data/cons [type-level]) bool bool-true
            (app (function/const* 'data/nil [type-level]) bool))))

;; matrix rows: row i0 is [1 1] (shared capacity), row i1 is [1 0] (line limit)
(def matrix
  (function/lam
   [['row bool]]
   (app (function/const* 'data/Bool.rec [type-level])
        (function/lam [['ignored bool]] (function/arrow bool signed))
        (pick (money 1 0) (money 1 0))
        (pick (money 1 0) (money 0 0))
        'row)))

(def capacities (pick (money 4 0) (money 3 0)))   ; b = (4, 3)
(def margins (pick (money 2 0) (money 0 1)))      ; c = (2, -1)  <- the penalty
(def plan (pick (money 3 0) (money 0 0)))         ; x = (3, 0)
(def prices (pick (money 0 0) (money 2 0)))       ; y = (0, 2)

(defn- row-activity [i]
  (map-sum bool (function/lam [['j bool]]
                              (smul (app (app matrix i) 'j) (app plan 'j))) index-list))

(defn- column-price [j]
  (map-sum bool (function/lam [['i bool]]
                              (smul (app (app matrix 'i) j) (app prices 'i))) index-list))

(def primal-objective
  (map-sum bool (function/lam [['j bool]]
                              (smul (app margins 'j) (app plan 'j))) index-list))

(def dual-objective
  (map-sum bool (function/lam [['i bool]]
                              (smul (app capacities 'i) (app prices 'i))) index-list))

;; ---- discharging the hypotheses by computation -----------------------------

(defn- decided-at-most
  "`a <= b` proved by running the decision procedure and recording that it
  returned true."
  [a b]
  (app (function/const* 'signed/decide-at-most-true-sound []) a b
       (app (function/const* 'equality/reflexive [type-level]) bool bool-true)))

(defn- for-both
  "A proof of `forall index : Bool, motive index` from the two cases."
  [motive at-false at-true]
  (function/lam
   [['index bool]]
   (app (function/const* 'data/Bool.rec [zero-level]) motive at-false at-true
        'index)))

(def primal-feasible
  (for-both
   (function/lam [['i bool]] (sle (row-activity 'i) (app capacities 'i)))
   (decided-at-most (row-activity bool-false) (app capacities bool-false))
   (decided-at-most (row-activity bool-true) (app capacities bool-true))))

(def dual-feasible
  (for-both
   (function/lam [['j bool]] (sle (app margins 'j) (column-price 'j)))
   (decided-at-most (app margins bool-false) (column-price bool-false))
   (decided-at-most (app margins bool-true) (column-price bool-true))))

(def plan-nonnegative
  (for-both
   (function/lam [['j bool]] (sle signed-zero (app plan 'j)))
   (decided-at-most signed-zero (app plan bool-false))
   (decided-at-most signed-zero (app plan bool-true))))

(def prices-nonnegative
  (for-both
   (function/lam [['i bool]] (sle signed-zero (app prices 'i)))
   (decided-at-most signed-zero (app prices bool-false))
   (decided-at-most signed-zero (app prices bool-true))))

;; both objectives compute to 6, so the cross product of the equivalence is a
;; nat identity between two numerals and reflexivity closes it
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rnum [v] (app (function/const* 'nnrat/numerator []) v))
(defn- rden [v] (app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))

(defn- computed-equivalence [left right]
  (app (function/const* 'equality/reflexive [type-level]) nat
       (nmul (rnum (radd (pos left) (neg right)))
             (rden (radd (pos right) (neg left))))))

(def zero-gap (computed-equivalence dual-objective primal-objective))

;; ---- the certificate --------------------------------------------------------

(def worked-optimal-spec
  {:name 'optimization/signed-lp-worked-optimal :universes []
   :type
   (function/forall
    [['candidate (function/arrow bool signed)]
     ['candidate-feasible
      (function/forall
       [['i bool]]
       (sle (map-sum bool
                     (function/lam [['j bool]]
                                   (smul (app (app matrix 'i) 'j)
                                         (app 'candidate 'j)))
                     index-list)
            (app capacities 'i)))]
     ['candidate-nonnegative
      (function/forall [['j bool]] (sle signed-zero (app 'candidate 'j)))]]
    (sle (map-sum bool
                  (function/lam [['j bool]]
                                (smul (app margins 'j) (app 'candidate 'j)))
                  index-list)
         primal-objective))
   :value
   (function/lam
    [['candidate (function/arrow bool signed)]
     ['candidate-feasible
      (function/forall
       [['i bool]]
       (sle (map-sum bool
                     (function/lam [['j bool]]
                                   (smul (app (app matrix 'i) 'j)
                                         (app 'candidate 'j)))
                     index-list)
            (app capacities 'i)))]
     ['candidate-nonnegative
      (function/forall [['j bool]] (sle signed-zero (app 'candidate 'j)))]]
    (app (function/const* 'optimization/signed-lp-optimality-certificate
                          [zero-level])
         bool bool matrix capacities margins plan prices index-list index-list
         primal-feasible dual-feasible plan-nonnegative prices-nonnegative
         zero-gap 'candidate 'candidate-feasible 'candidate-nonnegative))})

;; the certified optimum, stated as a number rather than as an expression
(def worked-value-spec
  {:name 'optimization/signed-lp-worked-value :universes []
   :type (seq-equiv primal-objective (money 6 0))
   :value (computed-equivalence primal-objective (money 6 0))})

(def worked-bound-spec
  {:name 'optimization/signed-lp-worked-dual-bound :universes []
   :type (sle primal-objective dual-objective)
   :value (app (function/const* 'optimization/signed-lp-weak-duality [zero-level])
               bool bool matrix capacities margins plan prices
               index-list index-list
               primal-feasible dual-feasible plan-nonnegative
               prices-nonnegative)})

(def definition-specs [])
(def theorem-specs [worked-bound-spec worked-value-spec worked-optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      lp/extend-environment
      decide/extend-environment
      (support/extend-with :signed-lp-certificate theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
