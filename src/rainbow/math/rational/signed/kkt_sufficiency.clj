(ns rainbow.math.rational.signed.kkt-sufficiency
  "KKT sufficiency: a stationary, feasible, complementary point is a global
  optimum of a convex program.

  The Karush-Kuhn-Tucker conditions at a candidate `x0` are, in this
  presentation:

    STATIONARITY   the Lagrangian L y = f y + penalty y has a supporting linear
                   certificate at x0 that holds for every y (not only feasible
                   y): L x0 + linear y <= L y, with 0 <= linear y.
    FEASIBILITY    x0 is feasible, and the penalty is nonpositive on the
                   feasible set (dual feasibility, lambda >= 0, plus constraint
                   satisfaction).
    COMPLEMENTARITY  penalty x0 ~ 0.

  The conclusion is global primal optimality: f x0 <= f x for every feasible x.
  No local search, no derivative calculus, no convexity of the feasible set is
  used -- only the order laws.

  The proof is exactly the composition of the two preceding modules.  The
  first-order theorem turns stationarity into `x0 minimizes the Lagrangian
  globally`, which is precisely the hypothesis Lagrangian weak duality needs;
  weak duality then bounds every feasible objective value below by L x0, and
  complementarity rewrites L x0 as f x0.

  Native and axiom-free; chains signed convex optimality and signed Lagrangian
  duality on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-optimality :as convex]
            [rainbow.math.rational.signed.lagrangian-duality :as duality]))

(def signed (function/const* 'signed/SignedRational []))
(def objective (function/arrow signed signed))
(def predicate (function/arrow signed 'Prop))
(def signed-zero (function/const* 'signed/zero []))
(def truth (function/const* 'proposition/truth []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-refl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c first second))
(defn- rat-four [a b c d]
  (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))

;; c + a ~ c + b whenever a ~ b.  Signed equivalence is the nnrat equivalence
;; (Pc+Pa)+(Nc+Nb) ~ (Pc+Pb)+(Nc+Na); reorder both sides so the shared Pc+Nc
;; sits in front and rewrite the remaining summand with the hypothesis.
(def add-left-respects-spec
  {:name 'signed/add-left-respects-equivalence :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['same (seq-equiv 'a 'b)]]
          (seq-equiv (sadd 'c 'a) (sadd 'c 'b)))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['same (seq-equiv 'a 'b)]]
    (let [Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          Pc (pos 'c) Nc (neg 'c)
          shared (radd Pc Nc)
          start (radd (radd Pc Pa) (radd Nc Nb))
          middle-left (radd shared (radd Pa Nb))
          middle-right (radd shared (radd Pb Na))
          finish (radd (radd Pc Pb) (radd Nc Na))]
      (rat-trans
       start middle-left finish
       (rat-four Pc Pa Nc Nb)
       (rat-trans
        middle-left middle-right finish
        (rat-add-respects shared shared (radd Pa Nb) (radd Pb Na)
                          (rat-refl shared) 'same)
        (rat-sym finish middle-right (rat-four Pc Pb Nc Na))))))})

(defn- lagrangian [f penalty]
  (function/lam [['y signed]] (sadd (app f 'y) (app penalty 'y))))

(defn- stationarity-type [f penalty linear x0]
  (function/forall
   [['y signed]]
   (sle (sadd (sadd (app f x0) (app penalty x0)) (app linear 'y))
        (sadd (app f 'y) (app penalty 'y)))))

(defn- variational-type [linear]
  (function/forall [['y signed]] (sle signed-zero (app linear 'y))))

(defn- slack-type [penalty feasible]
  (function/forall [['y signed] ['member (app feasible 'y)]]
                   (sle (app penalty 'y) signed-zero)))

;; Stationarity says x0 minimizes the Lagrangian over the WHOLE space, so L x0
;; is an admissible dual value.  This is the first-order theorem applied with
;; the trivially-true feasibility predicate.
(def stationary-minimizes-lagrangian-spec
  {:name 'optimization/signed-stationary-minimizes-lagrangian :universes []
   :type
   (function/forall
    [['f objective] ['penalty objective] ['linear objective] ['x0 signed]
     ['stationarity (stationarity-type 'f 'penalty 'linear 'x0)]
     ['variational (variational-type 'linear)]
     ['y signed]]
    (sle (sadd (app 'f 'x0) (app 'penalty 'x0))
         (sadd (app 'f 'y) (app 'penalty 'y))))
   :value
   (function/lam
    [['f objective] ['penalty objective] ['linear objective] ['x0 signed]
     ['stationarity (stationarity-type 'f 'penalty 'linear 'x0)]
     ['variational (variational-type 'linear)]
     ['y signed]]
    (app (function/const*
          'optimization/signed-first-order-global-minimum [])
         (lagrangian 'f 'penalty) 'linear 'x0
         (function/lam [['z signed]] truth)
         (function/lam [['z signed] ['member truth]]
                       (app 'stationarity 'z))
         (function/lam [['z signed] ['member truth]]
                       (app 'variational 'z))
         'y trivial))})

;; The KKT conditions are sufficient for global optimality.
(def kkt-sufficiency-spec
  {:name 'optimization/signed-kkt-sufficiency :universes []
   :type
   (function/forall
    [['f objective] ['penalty objective] ['linear objective]
     ['feasible predicate] ['x0 signed]
     ['stationarity (stationarity-type 'f 'penalty 'linear 'x0)]
     ['variational (variational-type 'linear)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0-member (app 'feasible 'x0)]
     ['complementary (seq-equiv (app 'penalty 'x0) signed-zero)]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (app 'f 'x0) (app 'f 'x)))
   :value
   (function/lam
    [['f objective] ['penalty objective] ['linear objective]
     ['feasible predicate] ['x0 signed]
     ['stationarity (stationarity-type 'f 'penalty 'linear 'x0)]
     ['variational (variational-type 'linear)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0-member (app 'feasible 'x0)]
     ['complementary (seq-equiv (app 'penalty 'x0) signed-zero)]
     ['x signed] ['member (app 'feasible 'x)]]
    (let [f0 (app 'f 'x0)
          p0 (app 'penalty 'x0)
          fx (app 'f 'x)
          dual (sadd f0 p0)
          padded (sadd f0 signed-zero)
          bound
          (function/lam
           [['y signed]]
           (app (function/const*
                 'optimization/signed-stationary-minimizes-lagrangian [])
                'f 'penalty 'linear 'x0 'stationarity 'variational 'y))
          ;; every feasible objective value is bounded below by the dual value
          weak
          (app (function/const*
                'optimization/signed-lagrangian-weak-duality [])
               'f 'penalty 'feasible dual bound 'slack 'x 'member)
          ;; complementarity collapses the dual value to f x0, in two rewrites
          ;; so no signed equivalence transitivity is needed
          padded-below
          (signed-at-most-respects
           dual padded fx fx
           (app (function/const* 'signed/add-left-respects-equivalence [])
                p0 signed-zero f0 'complementary)
           (signed-refl fx)
           weak)]
      (signed-at-most-respects
       padded f0 fx fx
       (signed-add-zero-right f0)
       (signed-refl fx)
       padded-below)))})

(def definition-specs [])
(def theorem-specs
  [add-left-respects-spec
   stationary-minimizes-lagrangian-spec
   kkt-sufficiency-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex/extend-environment
      duality/extend-environment
      (support/extend-with :signed-kkt-sufficiency theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
