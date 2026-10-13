(ns rainbow.math.rational.nnrat.general-contraction
  "Arbitrary-gamma contraction convergence.  With a = ap+1, g = gp+1, gamma = a/(a+g)
  (any rational < 1) and the bound B n = a/(a+ng) = nnrat/general-harmonic ap gp n:

    nnrat/general-harmonic-step : gamma * B n <= B (n+1)
    analysis/general-contraction-error-below : e0 <= B 0 -> (forall n, e(n+1) <= gamma*e n)
                                             -> (forall n, e n <= B n)
    analysis/general-contraction-converges   : ... -> rate-null e

  The step inequality reduces (at-most-from-cross) to a nat cross-product whose gap is
  exactly a*n*g^2: after a succ-expansion (succ n)*g = g + n*g and a combine-law
  denominator transport, the witness W = a*n*g^2 and nat-ring close it.  The induction and
  the rate-null conclusion mirror the 1/2 case, with general-harmonic-null + null-dominated.
  Native and axiom-free; chains nnrat-general-harmonic, nnrat-multiply-monotone, nnrat-ring."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.general-harmonic :as gh]
            [rainbow.math.rational.nnrat.multiply-monotone :as mm]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))

(defn- app [f & args] (apply function/app f args))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- gh-seq [ap gp n] (function/app (function/const* 'nnrat/general-harmonic []) ap gp n))
(defn- from-cross [l r ord] (function/app (function/const* 'nnrat/at-most-from-cross []) l r ord))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- mult-succ-right [v f] (function/app (function/const* 'nat/multiply-successor-right []) v f))
(defn- mult-comm [a b] (function/app (function/const* 'nat/multiply-commutative []) a b))
(defn- combine-law [l r] (function/app (function/const* 'nnrat/denominator-combine []) l r))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- witness [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

;; gamma * B n <= B (n+1)
(def general-harmonic-step-spec
  {:name 'nnrat/general-harmonic-step :universes []
   :type (function/forall
          [['ap nat] ['gp nat] ['n nat]]
          (rat-at-most (rmul (make (succ 'ap) (nadd 'ap (succ 'gp)))   ; gamma = a/(a+g)
                             (gh-seq 'ap 'gp 'n))
                       (gh-seq 'ap 'gp (succ 'n))))
   :value
   (function/lam
    [['ap nat] ['gp nat] ['n nat]]
    (let [a (succ 'ap) g (succ 'gp)
          gamma (make a (nadd 'ap g))
          bn (gh-seq 'ap 'gp 'n)
          gbn (rmul gamma bn)
          bsn (gh-seq 'ap 'gp (succ 'n))
          ng (nmul 'n g)
          ;; base(gbn)(bsn) endpoints: X_act = (a*a)*DSN ; Y_act = a*DG
          DSN (nadd a (nmul (succ 'n) g))                       ; den(bsn) (defeq)
          DG-l (succ (nadd 'ap g)) DG-r (succ (nadd 'ap ng))    ; succ L, succ R (defeq a+g, a+ng)
          DSN-r (nadd a (nadd g (nmul g 'n)))                   ; a + g + g*n
          DG-red (nmul (nadd a g) (nadd a ng))                  ; (a+g)*(a+ng)
          X-act (nmul (nmul a a) DSN)
          Y-act (nmul a (succ (function/app (function/const* 'nnrat/combine-denominator-predecessors [])
                                            (nadd 'ap g) (nadd 'ap ng))))
          X-r (nmul (nmul a a) DSN-r)
          Y-r (nmul a DG-red)
          W (nmul a (nmul 'n (nmul g g)))
          ;; base-reduced : X-r <= Y-r  (witness W ; X-r + W = Y-r by nat-ring)
          base-reduced (witness (function/lam [['e nat]] (eq-nat (nadd X-r 'e) Y-r))
                                W (ring-eq (nadd X-r W) Y-r))
          ;; (succ n)*g = g + g*n
          sexp (transitive (nmul (succ 'n) g) (nmul g (succ 'n)) (nadd g (nmul g 'n))
                           (mult-comm (succ 'n) g) (mult-succ-right g 'n))
          eq-DSN (congruent (function/lam [['v nat]] (nadd a 'v)) (nmul (succ 'n) g) (nadd g (nmul g 'n)) sexp)
          eq-X (congruent (function/lam [['v nat]] (nmul (nmul a a) 'v)) DSN DSN-r eq-DSN)
          ;; DG = (a+g)*(a+ng) via combine law
          law (combine-law (nadd 'ap g) (nadd 'ap ng))          ; DG = (succ L)*(succ R)
          eq-Y (congruent (function/lam [['v nat]] (nmul a 'v))
                          (succ (function/app (function/const* 'nnrat/combine-denominator-predecessors [])
                                              (nadd 'ap g) (nadd 'ap ng)))
                          (nmul DG-l DG-r) law)
          ;; transport base-reduced -> base-actual
          step-a (rewrite-left X-act X-r Y-r eq-X base-reduced)
          step-b (rewrite-right X-act Y-r Y-act (symmetric Y-act Y-r eq-Y) step-a)]
      (from-cross gbn bsn step-b)))})

;; induction: e0 <= B 0 and e(n+1) <= gamma*e n  =>  e n <= B n
(def error-below-spec
  {:name 'analysis/general-contraction-error-below :universes []
   :type (function/forall
          [['ap nat] ['gp nat] ['e (function/arrow nat nnrat)]
           ['e0 (rat-at-most (app 'e zero-nat) (gh-seq 'ap 'gp zero-nat))]
           ['rec (function/forall [['n nat]]
                                  (rat-at-most (app 'e (succ 'n))
                                               (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (app 'e 'n))))]]
          (function/forall [['n nat]] (rat-at-most (app 'e 'n) (gh-seq 'ap 'gp 'n))))
   :value
   (function/lam
    [['ap nat] ['gp nat] ['e (function/arrow nat nnrat)]
     ['e0 (rat-at-most (app 'e zero-nat) (gh-seq 'ap 'gp zero-nat))]
     ['rec (function/forall [['n nat]]
                            (rat-at-most (app 'e (succ 'n))
                                         (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (app 'e 'n))))]]
    (let [gamma (make (succ 'ap) (nadd 'ap (succ 'gp)))]
      (function/lam
       [['n nat]]
       (function/app
        (function/const* 'data/Nat.rec [[:zero]])
        (function/lam [['m nat]] (rat-at-most (app 'e 'm) (gh-seq 'ap 'gp 'm)))
        'e0
        (function/lam
         [['prev nat] ['ih (rat-at-most (app 'e 'prev) (gh-seq 'ap 'gp 'prev))]]
         (function/app
          (function/const* 'nnrat/at-most-transitive [])
          (app 'e (succ 'prev)) (rmul gamma (gh-seq 'ap 'gp 'prev)) (gh-seq 'ap 'gp (succ 'prev))
          (function/app
           (function/const* 'nnrat/at-most-transitive [])
           (app 'e (succ 'prev)) (rmul gamma (app 'e 'prev)) (rmul gamma (gh-seq 'ap 'gp 'prev))
           (app 'rec 'prev)
           (function/app (function/const* 'nnrat/multiply-monotone [])
                         gamma (app 'e 'prev) (gh-seq 'ap 'gp 'prev) 'ih))
          (function/app (function/const* 'nnrat/general-harmonic-step []) 'ap 'gp 'prev)))
        'n))))})

;; capstone: arbitrary gamma < 1 contraction converges
(def general-contraction-converges-spec
  {:name 'analysis/general-contraction-converges :universes []
   :type (function/forall
          [['ap nat] ['gp nat] ['e (function/arrow nat nnrat)]
           ['e0 (rat-at-most (app 'e zero-nat) (gh-seq 'ap 'gp zero-nat))]
           ['rec (function/forall [['n nat]]
                                  (rat-at-most (app 'e (succ 'n))
                                               (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (app 'e 'n))))]]
          (function/app (function/const* 'analysis/rate-null [])
                        'e (function/lam [['k nat]] (nmul (succ 'ap) 'k))))
   :value
   (function/lam
    [['ap nat] ['gp nat] ['e (function/arrow nat nnrat)]
     ['e0 (rat-at-most (app 'e zero-nat) (gh-seq 'ap 'gp zero-nat))]
     ['rec (function/forall [['n nat]]
                            (rat-at-most (app 'e (succ 'n))
                                         (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (app 'e 'n))))]]
    (function/app
     (function/const* 'analysis/rate-null-dominated [])
     (function/app (function/const* 'nnrat/general-harmonic []) 'ap 'gp)
     'e
     (function/lam [['k nat]] (nmul (succ 'ap) 'k))
     (function/app (function/const* 'analysis/general-contraction-error-below [])
                   'ap 'gp 'e 'e0 'rec)
     (function/app (function/const* 'analysis/general-harmonic-null []) 'ap 'gp)))})

(def definition-specs [])
(def theorem-specs [general-harmonic-step-spec error-below-spec
                    general-contraction-converges-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.general-harmonic rainbow.math.rational.nnrat.multiply-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-general-contraction (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.general-contraction))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
