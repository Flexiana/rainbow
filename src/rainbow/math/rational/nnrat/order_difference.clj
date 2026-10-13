(ns rainbow.math.rational.nnrat.order-difference
  "Nonnegative-rational order is difference-existence, and the two-point
  rearrangement inequality that follows from it.

  `nnrat/at-most` is the reflexive-transitive closure of a cross-product nat
  comparison, so it carries no additive witness on its face.  But nat order
  DOES: `nat/at-most a b` is `exists e, a + e = b`.  Transporting that witness
  through the cross product yields

      nnrat/at-most-difference :  x <= y  ->  exists w, x + w ~ y

  with the explicit witness `w = e / (den x * den y)`.  Verifying it is a single
  nat-ring identity around the extracted equation:

      (num x * (dx*dy) + e*dx) * dy = (dx*dy) * (num x * dy + e)
                                    = (dx*dy) * (num y * dx)
                                    = num y * (dx * (dx*dy)).

  The payoff is the TWO-POINT REARRANGEMENT INEQUALITY

      nnrat/rearrangement-two-point :  n <= p  ->  q <= m
                                       ->  p*q + n*m  <=  p*m + n*q

  -- pairing the larger factor with the larger factor dominates the crossed
  pairing.  It is the multiplicative order fact that no amount of termwise
  monotonicity can reach (the two terms move in opposite directions), and it is
  exactly the sign rule `(p-n)*(m-q) >= 0` stated without subtraction.  Writing
  p as n+u turns the goal into `u*q <= u*m` plus additive regrouping, which is
  ordinary monotonicity.

  Native and axiom-free; chains the nnrat order toolkit, the nat-ring tactic (for
  the witness identity) and the nnrat-ring tactic (for the two regroupings) on
  D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.add-monotone :as am]
            [rainbow.math.rational.nnrat.additive-reassociation :as rr]
            [rainbow.math.rational.nnrat.distribute-right :as dist]
            [rainbow.math.rational.nnrat.multiply-monotone :as mm]
            [rainbow.math.rational.nnrat.order-equivalence :as oe]
            [rainbow.math.rational.nnrat.ring :as nnring]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & args] (apply function/app f args))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nsucc [v] (app (function/const* 'data/succ []) v))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))

(defn- rnum [v] (app (function/const* 'nnrat/numerator []) v))
(defn- dpre [v] (app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- rmake [n dp] (app (function/const* 'nnrat/make []) n dp))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- rat-le [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- base-le [a b] (app (function/const* 'nnrat/base-at-most []) a b))
(defn- equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- combine [a b]
  (app (function/const* 'nnrat/combine-denominator-predecessors []) a b))

(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))
(defn- nat-transitive [l m r p q]
  (app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- nat-congruent [mapping l r same]
  (app (function/const* 'equality/congruent-function [type-level type-level])
       nat nat mapping l r same))

(defn- existence [pred]
  (app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- use-witness [pred goal exists handler]
  (app (function/const* 'proposition/use-witness [type-level])
       nnrat pred goal exists handler))
(defn- witness [pred value proof]
  (app (function/const* 'proposition/witness [type-level]) nnrat pred value proof))
(defn- nat-use-witness [pred goal exists handler]
  (app (function/const* 'proposition/use-witness [type-level])
       nat pred goal exists handler))

(defn- rat-refl [v] (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c first second))
(defn- rat-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-assoc [a b c] (app (function/const* 'nnrat/add-associative []) a b c))
(defn- rat-swap [a b c] (app (function/const* 'nnrat/add-swap-right []) a b c))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-mul-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- rat-to-cross [a b h]
  (app (function/const* 'nnrat/at-most-to-cross []) a b h))
(defn- rat-mul-monotone [c a b h]
  (app (function/const* 'nnrat/multiply-monotone []) c a b h))
(defn- rat-add-right-monotone [c a b h]
  (app (function/const* 'nnrat/add-right-monotone []) c a b h))
(defn- dist-right [a b m]
  (app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))

;; ---- order as difference-existence -----------------------------------------

(defn- difference-predicate [x y]
  (function/lam [['w nnrat]] (equiv (radd x 'w) y)))

(def at-most-difference-spec
  {:name 'nnrat/at-most-difference :universes []
   :type (function/forall
          [['x nnrat] ['y nnrat] ['ordered (rat-le 'x 'y)]]
          (existence (difference-predicate 'x 'y)))
   :value
   (function/lam
    [['x nnrat] ['y nnrat] ['ordered (rat-le 'x 'y)]]
    (let [nx (rnum 'x) dpx (dpre 'x) dx (nsucc dpx)
          ny (rnum 'y) dpy (dpre 'y) dy (nsucc dpy)
          left-cross (nmul nx dy)
          right-cross (nmul ny dx)
          goal (existence (difference-predicate 'x 'y))]
      (nat-use-witness
       (function/lam [['e nat]] (eq-nat (nadd left-cross 'e) right-cross))
       goal
       (rat-to-cross 'x 'y 'ordered)
       (function/lam
        [['e nat] ['he (eq-nat (nadd left-cross 'e) right-cross)]]
        (let [w (rmake 'e (combine dpx dpy))
              shared (nmul dx dy)
              ;; (num x * (dx*dy) + e*dx) * dy  ~  num y * (dx * (dx*dy))
              start (nmul (nadd (nmul nx shared) (nmul 'e dx)) dy)
              middle-left (nmul shared (nadd left-cross 'e))
              middle-right (nmul shared right-cross)
              finish (nmul ny (nmul dx shared))
              proof
              (nat-transitive
               start middle-left finish
               (ring-eq start middle-left)
               (nat-transitive
                middle-left middle-right finish
                (nat-congruent
                 (function/lam [['hole nat]] (nmul shared 'hole))
                 (nadd left-cross 'e) right-cross 'he)
                (ring-eq middle-right finish)))]
          (witness (difference-predicate 'x 'y) w proof))))))})

;; ---- two-point rearrangement -----------------------------------------------

(def rearrangement-two-point-spec
  {:name 'nnrat/rearrangement-two-point :universes []
   :type (function/forall
          [['n nnrat] ['p nnrat] ['q nnrat] ['m nnrat]
           ['hnp (rat-le 'n 'p)]
           ['hqm (rat-le 'q 'm)]]
          (rat-le (radd (rmul 'p 'q) (rmul 'n 'm))
                  (radd (rmul 'p 'm) (rmul 'n 'q))))
   :value
   (function/lam
    [['n nnrat] ['p nnrat] ['q nnrat] ['m nnrat]
     ['hnp (rat-le 'n 'p)]
     ['hqm (rat-le 'q 'm)]]
    (let [goal (rat-le (radd (rmul 'p 'q) (rmul 'n 'm))
                       (radd (rmul 'p 'm) (rmul 'n 'q)))]
      (use-witness
       (difference-predicate 'n 'p)
       goal
       (app (function/const* 'nnrat/at-most-difference []) 'n 'p 'hnp)
       (function/lam
        [['u nnrat] ['hu (equiv (radd 'n 'u) 'p)]]
        (let [sum-n-u (radd 'n 'u)
              p-back (rat-sym sum-n-u 'p 'hu)   ; p ~ n+u
              nq (rmul 'n 'q) nm (rmul 'n 'm)
              uq (rmul 'u 'q) um (rmul 'u 'm)
              core (radd nq nm)
              left-side (radd (rmul 'p 'q) nm)
              right-side (radd (rmul 'p 'm) nq)
              target-left (radd uq core)
              target-right (radd um core)

              ;; p*q + n*m ~ (n+u)*q + n*m ~ u*q + (n*q + n*m):
              ;; substitute p, then one semiring normalization
              substituted-left (radd (rmul sum-n-u 'q) nm)
              left-same
              (rat-trans
               left-side substituted-left target-left
               (rat-add-respects
                (rmul 'p 'q) (rmul sum-n-u 'q) nm nm
                (rat-mul-respects 'p sum-n-u 'q 'q p-back (rat-refl 'q))
                (rat-refl nm))
               (nnring/equiv substituted-left target-left))

              ;; p*m + n*q ~ (n+u)*m + n*q ~ u*m + (n*q + n*m)
              substituted-right (radd (rmul sum-n-u 'm) nq)
              right-same
              (rat-trans
               right-side substituted-right target-right
               (rat-add-respects
                (rmul 'p 'm) (rmul sum-n-u 'm) nq nq
                (rat-mul-respects 'p sum-n-u 'm 'm p-back (rat-refl 'm))
                (rat-refl nq))
               (nnring/equiv substituted-right target-right))

              ;; u*q <= u*m lifts to the two regrouped sums
              scaled (rat-mul-monotone 'u 'q 'm 'hqm)
              ordered (rat-add-right-monotone core uq um scaled)]
          (rat-at-most-respects left-side target-left right-side target-right
                                left-same right-same ordered))))))})

(def definition-specs [])
(def theorem-specs [at-most-difference-spec rearrangement-two-point-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.multiply-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-order-difference theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.order-difference))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
