(ns rainbow.math.rational.nnrat.farkas-both-sides
  "Brick 5d-ii of the general LP strong-duality Fourier-Motzkin encoding
 : converting a both-sides row into a
  clean affine lower row, subtraction-free.

  Eliminating the SECOND variable, brick 5d-i's cross conditions carry the
  surviving variable v on BOTH sides: A*v + P <= B*v + Q. That is not a
  brick-4/5b affine row. But when A <= B, the difference witness
  D (with A + D ~ B, from nnrat/at-most-difference) makes it one:
  B*v ~ (A+D)*v ~ A*v + D*v, so A*v + P <= A*v + (D*v + Q), and cancelling
  the common A*v (subtraction-free, via commute + at-most-add-right-cancel)
  leaves P <= D*v + Q -- an affine LOWER row in v (brick 5b shape).

  nnrat/farkas-both-sides-to-lower takes the difference witness D (A+D~B)
  explicitly, so the caller supplies it from at-most-difference once A <= B
  is known. This unblocks the second elimination: cross rows with A_i <= B_i
  become affine lower rows in x2, eliminable by brick 5b (the A_i >= B_i
  case is the symmetric affine-upper mirror). Native proof data,
  axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- erefl [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- esym [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- etrans [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- add-associative [a b c]
  (function/app (function/const* 'nnrat/add-associative []) a b c))
(defn- add-commutative [a b]
  (function/app (function/const* 'nnrat/add-commutative []) a b))
(defn- add-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- mul-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- distribute-right [a b m]
  (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(defn- at-most-respects [left eq-left right eq-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left eq-left right eq-right same-left same-right ordered))
(defn- at-most-add-right-cancel [x k y h]
  (function/app (function/const* 'nnrat/at-most-add-right-cancel []) x k y h))

(def both-sides-to-lower-spec
  {:name 'nnrat/farkas-both-sides-to-lower
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['diff (function/app (function/const* 'nnrat/equivalent [])
                          (add 'a 'd) 'b)]
     ['both-sides (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (at-most 'p (add (mul 'd 'v) 'q)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['diff (function/app (function/const* 'nnrat/equivalent [])
                          (add 'a 'd) 'b)]
     ['both-sides (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (let [av (mul 'a 'v)
          dv (mul 'd 'v)
          bv (mul 'b 'v)
          dvq (add dv 'q)
          av+dv (add av dv)
          ;; B*v ~ (A+D)*v ~ A*v + D*v
          bv-eq (etrans bv (mul (add 'a 'd) 'v) av+dv
                        (mul-respects 'b (add 'a 'd) 'v 'v
                                      (esym (add 'a 'd) 'b 'diff) (erefl 'v))
                        (distribute-right 'a 'd 'v))
          ;; hyp: av + p <= bv + q  ->  av + p <= (av+dv) + q
          hyp2 (at-most-respects
                (add av 'p) (add av 'p) (add av+dv 'q) (add bv 'q)
                (erefl (add av 'p))
                (add-respects av+dv bv 'q 'q (esym bv av+dv bv-eq) (erefl 'q))
                'both-sides)
          ;; reassoc RHS: (av+dv)+q ~ av+(dv+q)
          hyp3 (at-most-respects
                (add av 'p) (add av 'p) (add av dvq) (add av+dv 'q)
                (erefl (add av 'p))
                (esym (add av+dv 'q) (add av dvq) (add-associative av dv 'q))
                hyp2)
          ;; commute both endpoints: p + av <= (dv+q) + av
          hyp4 (at-most-respects
                (add 'p av) (add av 'p) (add dvq av) (add av dvq)
                (add-commutative 'p av)
                (add-commutative dvq av)
                hyp3)]
      ;; cancel av on the right
      (at-most-add-right-cancel 'p av dvq hyp4)))})

;; The mirror: when B <= A (difference witness B + D ~ A), the both-sides row
;; A*v + P <= B*v + Q converts to the affine UPPER row D*v + P <= Q (v bounded
;; above). Needed so the recursive reduction can case-split each cross
;; condition on A vs B: A<=B gives an affine lower row (to-lower), B<=A an
;; affine upper row (this).
(def both-sides-to-upper-spec
  {:name 'nnrat/farkas-both-sides-to-upper
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['diff (function/app (function/const* 'nnrat/equivalent [])
                          (add 'b 'd) 'a)]
     ['both-sides (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (at-most (add (mul 'd 'v) 'p) 'q))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['diff (function/app (function/const* 'nnrat/equivalent [])
                          (add 'b 'd) 'a)]
     ['both-sides (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (let [av (mul 'a 'v)
          bv (mul 'b 'v)
          dv (mul 'd 'v)
          dvp (add dv 'p)
          bv+dv (add bv dv)
          ;; A*v ~ (B+D)*v ~ B*v + D*v
          av-eq (etrans av (mul (add 'b 'd) 'v) bv+dv
                        (mul-respects 'a (add 'b 'd) 'v 'v
                                      (esym (add 'b 'd) 'a 'diff) (erefl 'v))
                        (distribute-right 'b 'd 'v))
          ;; hyp: av + p <= bv + q  ->  (bv+dv) + p <= bv + q
          hyp2 (at-most-respects
                (add bv+dv 'p) (add av 'p) (add bv 'q) (add bv 'q)
                (add-respects bv+dv av 'p 'p (esym av bv+dv av-eq) (erefl 'p))
                (erefl (add bv 'q))
                'both-sides)
          ;; reassoc LHS: (bv+dv)+p ~ bv+(dv+p)
          hyp3 (at-most-respects
                (add bv dvp) (add bv+dv 'p) (add bv 'q) (add bv 'q)
                (esym (add bv+dv 'p) (add bv dvp) (add-associative bv dv 'p))
                (erefl (add bv 'q))
                hyp2)
          ;; commute both endpoints: (dv+p) + bv <= q + bv
          hyp4 (at-most-respects
                (add dvp bv) (add bv dvp) (add 'q bv) (add bv 'q)
                (add-commutative dvp bv)
                (add-commutative 'q bv)
                hyp3)]
      ;; cancel bv on the right
      (at-most-add-right-cancel dvp bv 'q hyp4)))})

(def definition-specs [])
(def theorem-specs [both-sides-to-lower-spec both-sides-to-upper-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.add-cancellation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-both-sides (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-both-sides))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
