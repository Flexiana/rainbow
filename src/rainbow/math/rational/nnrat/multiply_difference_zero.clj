(ns rainbow.math.rational.nnrat.multiply-difference-zero
  "General nnrat discriminant (both-ordered case):
     nnrat/multiply-difference-zero-ordered :
       N1<=P1 -> N2<=P2 -> (P1*P2 + N1*N2 ~ P1*N2 + N1*P2) -> (P1 ~ N1) or (P2 ~ N2).
  With m1 = P1 monus N1, m2 = P2 monus N2 (so mi+Ni ~ Pi), the ring identity
  (m1+N1)(m2+N2) + N1*N2 ~ ((m1+N1)N2 + N1(m2+N2)) + m1*m2 exhibits m1*m2 as the gap; cancelling it
  gives m1*m2 ~ 0, and nnrat/multiply-zero-split splits it into m1~0 or m2~0, i.e. P1~N1 or P2~N2.
  Generalizes nnrat/square-difference-zero to distinct factors (the general no-zero-divisors core)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.multiply-zero-split :as mzs]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.monus :as nnrat-monus]
            [rainbow.math.rational.nnrat.add-cancel-zero :as add-cancel]
            [rainbow.math.rational.nnrat.order-total :as order-total]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- rmonus [a b] (app (function/const* 'nnrat/monus []) a b))
(defn- eqv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nle [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- erefl [x] (app (function/const* 'nnrat/equivalent-reflexive []) x))
(defn- esym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- etr [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- mresp [l le r re hl hr] (app (function/const* 'nnrat/multiply-respects-equivalence []) l le r re hl hr))
(defn- aresp [l le r re hl hr] (app (function/const* 'nnrat/add-respects-equivalence []) l le r re hl hr))
(defn- monus-add-cancel [p q h] (app (function/const* 'nnrat/monus-add-cancel []) p q h))
(defn- add-cancel-to-zero [a g h] (app (function/const* 'nnrat/add-cancel-to-zero []) a g h))
(defn- add-zero-left [x] (app (function/const* 'nnrat/add-zero-left []) x))
(defn- mult-zero-split [m1 m2 h] (app (function/const* 'nnrat/multiply-zero-split []) m1 m2 h))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))

;; From mi~0 (Qi = mi+Ni, e: Qi~Pi) conclude Pi~Ni.
(defn- p-from-m [P N m Q e z]
  (let [qN (etr Q (radd nnzero N) N (aresp m nnzero N N z (erefl N)) (add-zero-left N))] ; Q ~ N
    (etr P Q N (esym Q P e) qN)))                                                          ; P ~ Q ~ N

(def ordered-spec
  {:name 'nnrat/multiply-difference-zero-ordered
   :universes []
   :type (function/forall
          [['p1 nnrat] ['n1 nnrat] ['p2 nnrat] ['n2 nnrat]
           ['hle1 (nle 'n1 'p1)] ['hle2 (nle 'n2 'p2)]
           ['h (eqv (radd (rmul 'p1 'p2) (rmul 'n1 'n2)) (radd (rmul 'p1 'n2) (rmul 'n1 'p2)))]]
          (disjt (eqv 'p1 'n1) (eqv 'p2 'n2)))
   :value
   (function/lam
    [['p1 nnrat] ['n1 nnrat] ['p2 nnrat] ['n2 nnrat]
     ['hle1 (nle 'n1 'p1)] ['hle2 (nle 'n2 'p2)]
     ['h (eqv (radd (rmul 'p1 'p2) (rmul 'n1 'n2)) (radd (rmul 'p1 'n2) (rmul 'n1 'p2)))]]
    (let [P1 'p1 N1 'n1 P2 'p2 N2 'n2
          m1 (rmonus P1 N1) m2 (rmonus P2 N2)
          Q1 (radd m1 N1) Q2 (radd m2 N2)
          e1 (monus-add-cancel P1 N1 'hle1)   ; Q1 ~ P1
          e2 (monus-add-cancel P2 N2 'hle2)   ; Q2 ~ P2
          LHSq (radd (rmul Q1 Q2) (rmul N1 N2))
          RHSq (radd (rmul Q1 N2) (rmul N1 Q2))
          LHSp (radd (rmul P1 P2) (rmul N1 N2))
          RHSp (radd (rmul P1 N2) (rmul N1 P2))
          lhsqp (aresp (rmul Q1 Q2) (rmul P1 P2) (rmul N1 N2) (rmul N1 N2)
                       (mresp Q1 P1 Q2 P2 e1 e2) (erefl (rmul N1 N2)))            ; LHSq ~ LHSp
          rhsqp (aresp (rmul Q1 N2) (rmul P1 N2) (rmul N1 Q2) (rmul N1 P2)
                       (mresp Q1 P1 N2 N2 e1 (erefl N2))
                       (mresp N1 N1 Q2 P2 (erefl N1) e2))                          ; RHSq ~ RHSp
          hQ (etr LHSq LHSp RHSq lhsqp (etr LHSp RHSp RHSq 'h (esym RHSq RHSp rhsqp))) ; LHSq ~ RHSq
          rid (ring/equiv LHSq (radd RHSq (rmul m1 m2)))                           ; LHSq ~ RHSq + m1*m2
          step (etr RHSq LHSq (radd RHSq (rmul m1 m2)) (esym LHSq RHSq hQ) rid)    ; RHSq ~ RHSq + m1*m2
          mm0 (add-cancel-to-zero RHSq (rmul m1 m2)
                                  (esym RHSq (radd RHSq (rmul m1 m2)) step))       ; m1*m2 ~ 0
          split (mult-zero-split m1 m2 mm0)                                        ; (m1~0) or (m2~0)
          goal (disjt (eqv P1 N1) (eqv P2 N2))]
      (use-disj (eqv m1 nnzero) (eqv m2 nnzero) goal split
                (function/lam [['z1 (eqv m1 nnzero)]]
                              (left-disj (eqv P1 N1) (eqv P2 N2) (p-from-m P1 N1 m1 Q1 e1 'z1)))
                (function/lam [['z2 (eqv m2 nnzero)]]
                              (right-disj (eqv P1 N1) (eqv P2 N2) (p-from-m P2 N2 m2 Q2 e2 'z2))))))})

(defn- add-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- at-most-total [a b] (app (function/const* 'nnrat/at-most-total []) a b))
(defn- ordered [p1 n1 p2 n2 h1 h2 h]
  (app (function/const* 'nnrat/multiply-difference-zero-ordered []) p1 n1 p2 n2 h1 h2 h))

(def difference-zero-spec
  {:name 'nnrat/multiply-difference-zero
   :universes []
   :type (function/forall
          [['p1 nnrat] ['n1 nnrat] ['p2 nnrat] ['n2 nnrat]
           ['h (eqv (radd (rmul 'p1 'p2) (rmul 'n1 'n2)) (radd (rmul 'p1 'n2) (rmul 'n1 'p2)))]]
          (disjt (eqv 'p1 'n1) (eqv 'p2 'n2)))
   :value
   (function/lam
    [['p1 nnrat] ['n1 nnrat] ['p2 nnrat] ['n2 nnrat]
     ['h (eqv (radd (rmul 'p1 'p2) (rmul 'n1 'n2)) (radd (rmul 'p1 'n2) (rmul 'n1 'p2)))]]
    (let [P1 'p1 N1 'n1 P2 'p2 N2 'n2
          LHSh (radd (rmul P1 P2) (rmul N1 N2))
          RHSh (radd (rmul P1 N2) (rmul N1 P2))
          goal (disjt (eqv P1 N1) (eqv P2 N2))
          ;; hypothesis reorderings (add-commutative only; terms unchanged)
          hC (etr (radd (rmul N1 P2) (rmul P1 N2)) RHSh (radd (rmul N1 N2) (rmul P1 P2))
                  (add-comm (rmul N1 P2) (rmul P1 N2))
                  (etr RHSh LHSh (radd (rmul N1 N2) (rmul P1 P2))
                       (esym LHSh RHSh 'h) (add-comm (rmul P1 P2) (rmul N1 N2))))
          hD (etr (radd (rmul N1 N2) (rmul P1 P2)) LHSh (radd (rmul N1 P2) (rmul P1 N2))
                  (add-comm (rmul N1 N2) (rmul P1 P2))
                  (etr LHSh RHSh (radd (rmul N1 P2) (rmul P1 N2))
                       'h (add-comm (rmul P1 N2) (rmul N1 P2))))]
      (app (at-most-total N1 P1) goal
           (function/lam [['hle1 (nle N1 P1)]]
                         (app (at-most-total N2 P2) goal
                              (function/lam [['hle2 (nle N2 P2)]]                       ; case A
                                            (ordered P1 N1 P2 N2 'hle1 'hle2 'h))
                              (function/lam [['hleB (nle P2 N2)]]                       ; case B: P2<=N2
                                            (app (ordered P1 N1 N2 P2 'hle1 'hleB (esym LHSh RHSh 'h))
                                                 goal
                                                 (function/lam [['z (eqv P1 N1)]] (left-disj (eqv P1 N1) (eqv P2 N2) 'z))
                                                 (function/lam [['z (eqv N2 P2)]] (right-disj (eqv P1 N1) (eqv P2 N2) (esym N2 P2 'z)))))))
           (function/lam [['hleC (nle P1 N1)]]
                         (app (at-most-total N2 P2) goal
                              (function/lam [['hle2 (nle N2 P2)]]                       ; case C: P1<=N1
                                            (app (ordered N1 P1 P2 N2 'hleC 'hle2 hC)
                                                 goal
                                                 (function/lam [['z (eqv N1 P1)]] (left-disj (eqv P1 N1) (eqv P2 N2) (esym N1 P1 'z)))
                                                 (function/lam [['z (eqv P2 N2)]] (right-disj (eqv P1 N1) (eqv P2 N2) 'z))))
                              (function/lam [['hleD (nle P2 N2)]]                       ; case D: P1<=N1, P2<=N2
                                            (app (ordered N1 P1 N2 P2 'hleC 'hleD hD)
                                                 goal
                                                 (function/lam [['z (eqv N1 P1)]] (left-disj (eqv P1 N1) (eqv P2 N2) (esym N1 P1 'z)))
                                                 (function/lam [['z (eqv N2 P2)]] (right-disj (eqv P1 N1) (eqv P2 N2) (esym N2 P2 'z))))))))))})

(def theorem-specs [ordered-spec difference-zero-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      mzs/extend-environment
      identities/extend-environment
      nnrat-monus/extend-environment
      add-cancel/extend-environment
      order-total/extend-environment
      ring/extend-environment
      (support/extend-with :nnrat-multiply-difference-zero theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
