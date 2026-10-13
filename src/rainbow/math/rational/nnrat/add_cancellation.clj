(ns rainbow.math.rational.nnrat.add-cancellation
  "Real-analysis roadmap step 3: additive cancellation for the nnrat order --

    nnrat/at-most-add-right-cancel : (X + k) <= (Y + k) -> X <= Y

  the converse of add-monotonicity, and the piece signed order transitivity needs (it
  cancels the shared pos(b)+neg(b) term).  Strategy: drop the closure comparison to the
  base cross-product with step-2 nnrat/at-most-to-cross, cancel there, then lift back
  with nnrat/at-most-from-cross.

  At the base level base(X+k)(Y+k) reduces to a nat cross-product; transport the packed
  product-denominators succ(combine ..) to dX*dk / dY*dk via the nnrat/denominator-combine
  law, normalize both sides to (A + K) and (B + K) with the nat-ring tactic (K is the
  shared nk-term, equal on both sides as a monomial), cancel it additively (step-1a
  nat/at-most-add-right-cancel), then cancel the doubled positive factor dk = succ(dpre k)
  twice (step-1 nat/at-most-multiply-right-cancel) to reach nX*dY <= nY*dX = base X Y.

  Native and axiom-free; chains rainbow.math.rational.nnrat.order-equivalence (-> nat cancellation,
  nat-ring) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.order-equivalence :as oe]))

(def type-level [:succ [:zero]])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nat (function/const* 'data/Nat []))

(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- nsucc [v] (function/app (function/const* 'data/succ []) v))
(defn- base-at-most [p q] (function/app (function/const* 'nnrat/base-at-most []) p q))
(defn- rat-at-most [p q] (function/app (function/const* 'nnrat/at-most []) p q))
(defn- from-cross [l r ord] (function/app (function/const* 'nnrat/at-most-from-cross []) l r ord))
(defn- to-cross [l r h] (function/app (function/const* 'nnrat/at-most-to-cross []) l r h))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- add-right-cancel [a b k h]
  (function/app (function/const* 'nat/at-most-add-right-cancel []) a b k h))
(defn- mult-right-cancel [a b f h]
  (function/app (function/const* 'nat/at-most-multiply-right-cancel []) a b f h))
(defn- combine-law [l r]  ; succ(combine l r) = (succ l)*(succ r)
  (function/app (function/const* 'nnrat/denominator-combine []) l r))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

;; base-level additive cancellation: base (X+k) (Y+k) -> base X Y
(def base-add-cancel-spec
  {:name 'nnrat/base-at-most-add-right-cancel :universes []
   :type (function/forall
          [['x nnrat] ['k nnrat] ['y nnrat]
           ['hb (base-at-most (radd 'x 'k) (radd 'y 'k))]]
          (base-at-most 'x 'y))
   :value
   (function/lam
    [['x nnrat] ['k nnrat] ['y nnrat]
     ['hb (base-at-most (radd 'x 'k) (radd 'y 'k))]]
    (let [nX (num 'x) nY (num 'y) nk (num 'k)
          dpX (dpre 'x) dpY (dpre 'y) dpk (dpre 'k)
          dX (nsucc dpX) dY (nsucc dpY) dk (nsucc dpk)
          nXk (nadd (nmul nX dk) (nmul nk dX))   ; num(X+k)
          nYk (nadd (nmul nY dk) (nmul nk dY))   ; num(Y+k)
          DXk (nsucc (combine dpX dpk))          ; den(X+k) packed
          DYk (nsucc (combine dpY dpk))          ; den(Y+k) packed
          comb-x (combine-law dpX dpk)           ; DXk = dX*dk
          comb-y (combine-law dpY dpk)           ; DYk = dY*dk
          ;; canonical distributed monomials
          A (nmul (nmul (nmul nX dY) dk) dk)     ; ((nX*dY)*dk)*dk
          B (nmul (nmul (nmul nY dX) dk) dk)     ; ((nY*dX)*dk)*dk
          K (nmul (nmul (nmul nk dX) dY) dk)     ; shared nk term
          ;; hb : nXk*DYk <= nYk*DXk ; transport DYk -> dY*dk (left), DXk -> dX*dk (right)
          cong-l (congruent (function/lam [['v nat]] (nmul nXk 'v)) DYk (nmul dY dk) comb-y)
          h1a (rewrite-left (nmul nXk (nmul dY dk)) (nmul nXk DYk) (nmul nYk DXk)
                            (symmetric (nmul nXk DYk) (nmul nXk (nmul dY dk)) cong-l) 'hb)
          cong-r (congruent (function/lam [['v nat]] (nmul nYk 'v)) DXk (nmul dX dk) comb-x)
          h1 (rewrite-right (nmul nXk (nmul dY dk)) (nmul nYk DXk) (nmul nYk (nmul dX dk))
                            cong-r h1a)
          ;; normalize both sides to (A+K) and (B+K)
          h2a (rewrite-left (nadd A K) (nmul nXk (nmul dY dk)) (nmul nYk (nmul dX dk))
                            (ring-eq (nadd A K) (nmul nXk (nmul dY dk))) h1)
          h2 (rewrite-right (nadd A K) (nmul nYk (nmul dX dk)) (nadd B K)
                            (ring-eq (nmul nYk (nmul dX dk)) (nadd B K)) h2a)
          ;; cancel the shared additive K, then the doubled factor dk = succ dpk twice
          ab (add-right-cancel A B K h2)                              ; A <= B
          once (mult-right-cancel (nmul (nmul nX dY) dk) (nmul (nmul nY dX) dk) dpk ab)
          twice (mult-right-cancel (nmul nX dY) (nmul nY dX) dpk once)]
      twice))})

;; closure-level: (X+k) <= (Y+k) -> X <= Y
(def add-right-cancel-spec
  {:name 'nnrat/at-most-add-right-cancel :universes []
   :type (function/forall
          [['x nnrat] ['k nnrat] ['y nnrat]
           ['h (rat-at-most (radd 'x 'k) (radd 'y 'k))]]
          (rat-at-most 'x 'y))
   :value
   (function/lam
    [['x nnrat] ['k nnrat] ['y nnrat]
     ['h (rat-at-most (radd 'x 'k) (radd 'y 'k))]]
    (from-cross 'x 'y
                (function/app (function/const* 'nnrat/base-at-most-add-right-cancel [])
                              'x 'k 'y
                              (to-cross (radd 'x 'k) (radd 'y 'k) 'h))))})

(def definition-specs [])
(def theorem-specs [base-add-cancel-spec add-right-cancel-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-add-cancellation (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.add-cancellation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
