(ns rainbow.math.rational.nnrat.contraction-uniqueness
  "Banach fixed-point UNIQUENESS, the collapse half (the convergence half is
  nnrat-general-contraction).  For any rational gamma = a/(a+g) < 1 (a = ap+1,
  g = gp+1) and any x = nx/dx:

    nnrat/contraction-collapse : x <= gamma * x  ->  x ~ 0

  i.e. a nonnegative quantity dominated by its own gamma-contraction must be zero.
  Together with contraction-converges this pins the fixed point: if two fixed points
  x, y satisfy |x-y| <= gamma*|x-y| then |x-y| ~ 0, so x ~ y -- uniqueness.

  PROOF (all in the nat cross-product after at-most-to-cross):
    base(x)(gamma*x) is  nx * den(gamma*x) <= (a*nx) * dx.
    den(gamma*x) = succ(combine (ap+g) dxp) = (a+g)*dx  (denominator-combine law),
    so nat-ring puts it as  (a*M + g*M) <= a*M   with M = nx*dx.
    Pad the RHS to a*M + 0 and cancel the a*M prefix (at-most-add-left-cancel):
        g*M <= 0  ->  g*M = 0.
    g = succ gp reduces g*M to M + gp*M (multiply recurses on the LEFT arg), so
    sum-zero-left gives M = 0; M = nx*dx = nx + nx*dxp (multiply-successor-right on
    the right factor), sum-zero-left again gives nx = 0; and nx = 0 collapses the
    cross-product equivalence  nx*1 = 0*dx  (RHS reduces since 0*dx = 0).

  Native and axiom-free; chains nnrat-order-equivalence (to-cross + the nat additive
  cancellation and sum-zero-left bricks) and nat-ring."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.order-equivalence :as oe]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))

(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(def nnrat-zero (function/const* 'nnrat/zero []))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- combine-law [l r]
  (function/app (function/const* 'nnrat/denominator-combine []) l r))

(defn- to-cross [a b h]
  (function/app (function/const* 'nnrat/at-most-to-cross []) a b h))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- mult-succ-right [v f] (function/app (function/const* 'nat/multiply-successor-right []) v f))
(defn- mult-one-right [v] (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- add-zero-right [v] (function/app (function/const* 'algebra/nat-add-zero-right []) v))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- at-most-add-left-cancel [a b k h]
  (function/app (function/const* 'nat/at-most-add-left-cancel []) a b k h))
(defn- sum-zero-left [x y h]
  (function/app (function/const* 'nat/sum-zero-left []) x y h))
(defn- use-witness [pred goal exists handler]
  (function/app (function/const* 'proposition/use-witness [type-level]) nat pred goal exists handler))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

(def contraction-collapse-spec
  {:name 'nnrat/contraction-collapse :universes []
   :type (function/forall
          [['ap nat] ['gp nat] ['nx nat] ['dxp nat]
           ['h (rat-at-most (make 'nx 'dxp)
                            (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (make 'nx 'dxp)))]]
          (rat-equiv (make 'nx 'dxp) nnrat-zero))
   :value
   (function/lam
    [['ap nat] ['gp nat] ['nx nat] ['dxp nat]
     ['h (rat-at-most (make 'nx 'dxp)
                      (rmul (make (succ 'ap) (nadd 'ap (succ 'gp))) (make 'nx 'dxp)))]]
    (let [a (succ 'ap) g (succ 'gp) dx (succ 'dxp)
          gden-pred (nadd 'ap g)                    ; denominator-predecessor of gamma
          gamma (make a gden-pred)
          x (make 'nx 'dxp)
          gx (rmul gamma x)
          M (nmul 'nx dx)
          agsum (nadd a g)
          AM (nmul a M) GM (nmul g M)
          DenGX (succ (combine gden-pred 'dxp))     ; denominator of gamma*x
          numGX (nmul a 'nx)                        ; numerator of gamma*x
          ;; base(x)(gamma*x) : nx * DenGX <= numGX * dx
          cross (to-cross x gx 'h)
          ;; LHS: nx * DenGX = nx * ((a+g)*dx) = a*M + g*M
          eq1 (congruent (function/lam [['v nat]] (nmul 'nx 'v))
                         DenGX (nmul agsum dx) (combine-law gden-pred 'dxp))
          eq2 (ring-eq (nmul 'nx (nmul agsum dx)) (nadd AM GM))
          eqL (transitive (nmul 'nx DenGX) (nmul 'nx (nmul agsum dx)) (nadd AM GM) eq1 eq2)
          ;; RHS: numGX * dx = a*M
          eqR (ring-eq (nmul numGX dx) AM)
          ;; (a*M + g*M) <= a*M
          step-a (rewrite-left (nadd AM GM) (nmul 'nx DenGX) (nmul numGX dx)
                               (symmetric (nmul 'nx DenGX) (nadd AM GM) eqL) cross)
          step-b (rewrite-right (nadd AM GM) (nmul numGX dx) AM eqR step-a)
          ;; pad RHS to a*M + 0 and cancel the a*M prefix : g*M <= 0
          padded (rewrite-right (nadd AM GM) AM (nadd AM zero-nat)
                                (symmetric (nadd AM zero-nat) AM (add-zero-right AM)) step-b)
          gm-le-0 (at-most-add-left-cancel GM zero-nat AM padded)
          ;; g*M <= 0 -> g*M = 0
          gm-eq-0 (use-witness (function/lam [['e nat]] (eq-nat (nadd GM 'e) zero-nat))
                               (eq-nat GM zero-nat)
                               gm-le-0
                               (function/lam [['e nat] ['he (eq-nat (nadd GM 'e) zero-nat)]]
                                             (sum-zero-left GM 'e 'he)))
          ;; g*M = (succ gp)*M reduces to M + gp*M ; sum-zero-left : M = 0
          m-eq-0 (sum-zero-left M (nmul 'gp M) gm-eq-0)
          ;; M = nx*dx = nx*(succ dxp) = nx + nx*dxp ; sum-zero-left : nx = 0
          nx-expand (mult-succ-right 'nx 'dxp)      ; nx*(succ dxp) = nx + nx*dxp
          add-nx-0 (transitive (nadd 'nx (nmul 'nx 'dxp)) M zero-nat
                               (symmetric M (nadd 'nx (nmul 'nx 'dxp)) nx-expand) m-eq-0)
          nx-eq-0 (sum-zero-left 'nx (nmul 'nx 'dxp) add-nx-0)]
      ;; goal (equivalent x zero) reduces to  nx*1 = 0*dx ; RHS 0*dx = 0
      (transitive (nmul 'nx (succ zero-nat)) 'nx (nmul zero-nat dx)
                  (mult-one-right 'nx) nx-eq-0)))})

(def definition-specs [])
(def theorem-specs [contraction-collapse-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      oe/extend-environment
      (support/extend-with :nnrat-contraction-uniqueness
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
