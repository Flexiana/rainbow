(ns rainbow.math.rational.nnrat.square-difference-zero
  "The nnrat AM-GM discriminant, ordered case:
     nnrat/square-difference-zero-ordered : N<=P -> (P*P + N*N ~ P*N + N*P) -> P ~ N.
  Let m = P monus N, so (m+N) ~ P (monus-add-cancel). Transport the hypothesis to the (m+N)
  form; the ring identity (m+N)^2 + N^2 ~ ((m+N)N + N(m+N)) + m*m then exhibits m*m as the
  gap, and cancelling it (add-cancel-to-zero) gives m*m ~ 0, hence m ~ 0 (nnrat/square-zero),
  hence P ~ N. The unordered version wraps this with at-most-total."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.square-zero :as sqz]
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
(defn- square-zero [m h] (app (function/const* 'nnrat/square-zero []) m h))

(def square-difference-zero-ordered-spec
  {:name 'nnrat/square-difference-zero-ordered
   :universes []
   :type (function/forall
          [['p nnrat] ['n nnrat] ['hle (nle 'n 'p)]
           ['h (eqv (radd (rmul 'p 'p) (rmul 'n 'n)) (radd (rmul 'p 'n) (rmul 'n 'p)))]]
          (eqv 'p 'n))
   :value
   (function/lam
    [['p nnrat] ['n nnrat] ['hle (nle 'n 'p)]
     ['h (eqv (radd (rmul 'p 'p) (rmul 'n 'n)) (radd (rmul 'p 'n) (rmul 'n 'p)))]]
    (let [P 'p N 'n
          m (rmonus P N)
          Q (radd m N)
          e (monus-add-cancel P N 'hle)                 ; Q ~ P
          LHSq (radd (rmul Q Q) (rmul N N))
          RHSq (radd (rmul Q N) (rmul N Q))
          LHSp (radd (rmul P P) (rmul N N))
          RHSp (radd (rmul P N) (rmul N P))
          lhsqp (aresp (rmul Q Q) (rmul P P) (rmul N N) (rmul N N)
                       (mresp Q P Q P e e) (erefl (rmul N N)))        ; LHSq ~ LHSp
          rhsqp (aresp (rmul Q N) (rmul P N) (rmul N Q) (rmul N P)
                       (mresp Q P N N e (erefl N)) (mresp N N Q P (erefl N) e))  ; RHSq ~ RHSp
          hQ (etr LHSq LHSp RHSq lhsqp (etr LHSp RHSp RHSq 'h (esym RHSq RHSp rhsqp)))  ; LHSq ~ RHSq
          rid (ring/equiv LHSq (radd RHSq (rmul m m)))               ; LHSq ~ RHSq + m*m
          step (etr RHSq LHSq (radd RHSq (rmul m m)) (esym LHSq RHSq hQ) rid)  ; RHSq ~ RHSq + m*m
          mm0 (add-cancel-to-zero RHSq (rmul m m) (esym RHSq (radd RHSq (rmul m m)) step))  ; m*m ~ 0
          m0 (square-zero m mm0)                                      ; m ~ 0
          qN (etr Q (radd nnzero N) N
                  (aresp m nnzero N N m0 (erefl N)) (add-zero-left N))  ; Q ~ N
          ]
      (etr P Q N (esym Q P e) qN)))})                                 ; P ~ Q ~ N

(defn- add-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- at-most-total [a b] (app (function/const* 'nnrat/at-most-total []) a b))
(defn- ordered [p n hle h] (app (function/const* 'nnrat/square-difference-zero-ordered []) p n hle h))

(def square-difference-zero-spec
  {:name 'nnrat/square-difference-zero
   :universes []
   :type (function/forall
          [['p nnrat] ['n nnrat]
           ['h (eqv (radd (rmul 'p 'p) (rmul 'n 'n)) (radd (rmul 'p 'n) (rmul 'n 'p)))]]
          (eqv 'p 'n))
   :value
   (function/lam
    [['p nnrat] ['n nnrat]
     ['h (eqv (radd (rmul 'p 'p) (rmul 'n 'n)) (radd (rmul 'p 'n) (rmul 'n 'p)))]]
    (let [P 'p N 'n
          lhsP (radd (rmul P P) (rmul N N)) rhsP (radd (rmul P N) (rmul N P))
          ;; swapped hypothesis for the P<=N branch: N*N+P*P ~ N*P+P*N
          lhsN (radd (rmul N N) (rmul P P)) rhsN (radd (rmul N P) (rmul P N))
          hswap (etr lhsN rhsP rhsN
                     (etr lhsN lhsP rhsP (add-comm (rmul N N) (rmul P P)) 'h)
                     (add-comm (rmul P N) (rmul N P)))]   ; lhsN ~ lhsP ~ rhsP ~ rhsN
      (app (at-most-total N P) (eqv P N)
           (function/lam [['hle (nle N P)]] (ordered P N 'hle 'h))          ; N<=P
           (function/lam [['hle2 (nle P N)]]                                 ; P<=N
                         (esym N P (ordered N P 'hle2 hswap))))))})

(def theorem-specs [square-difference-zero-ordered-spec square-difference-zero-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      sqz/extend-environment
      identities/extend-environment
      nnrat-monus/extend-environment
      add-cancel/extend-environment
      order-total/extend-environment
      ring/extend-environment
      (support/extend-with :nnrat-square-difference-zero theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
