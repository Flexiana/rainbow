(ns rainbow.math.rational.nnrat.lp-gap
  "LP duality-gap decomposition over nonnegative rationals -- the identity behind
  complementary slackness.  Because nnrat has no subtraction, feasibility is
  stated as equality with an explicit nonnegative slack:

    primal:  (A x)_i + s_i ~ b_i        (s : slacks,        rows -> nnrat)
    dual:    c_j + r_j ~ (Aᵀy)_j         (r : reduced costs, cols -> nnrat)

    nnrat/lp-gap-decomposition :
      b.y ~ c.x + ( sum_j r_j x_j + sum_i s_i y_i )

  The dual objective exceeds the primal objective by exactly the total
  complementary-slackness term (a sum of nonnegative products r_j x_j and
  s_i y_i).  Combined with nnrat/add-zero-split + map-sum-zero-at-split, a zero
  gap forces every r_j x_j and s_i y_i to 0 -- complementary slackness.

  Proof: expand b.y termwise via the primal slack equality (dist-right +
  map-sum-add), swap the double sum (scale-right + Fubini map-sum-swap + one
  per-term reorder) to sum_j (Aᵀy)_j x_j, then expand via the dual equality; the
  three pieces chain and reassociate.  Native and axiom-free; chains
  nnrat-lp-weak-duality (which brings the whole finite-sum toolkit) on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.lp-weak-duality :as lp]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element] (function/app (function/const* 'data/List [data-level]) element))
(defn- arrow [a b] (function/arrow a b))
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- mul-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence []) l le r re sl sr))
(defn- add-assoc [a b c] (function/app (function/const* 'nnrat/add-associative []) a b c))
(defn- mul-assoc [a b c] (function/app (function/const* 'nnrat/multiply-associative []) a b c))
(defn- mul-comm [a b] (function/app (function/const* 'nnrat/multiply-commutative []) a b))
(defn- dist-right [a b m] (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(defn- app [f x] (function/app f x))
(defn- lam [v ty body] (function/lam [[v ty]] body))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-respects [A f g hfg xs]
  (function/app (function/const* 'nnrat/map-sum-respects-equivalence [U]) A f g hfg xs))
(defn- map-sum-add [A f g xs]
  (function/app (function/const* 'nnrat/map-sum-add [U]) A f g xs))
(defn- scale-right [A f c xs]
  (function/app (function/const* 'nnrat/map-sum-scale-right [U]) A f c xs))
(defn- swap [A B F is js]
  (function/app (function/const* 'nnrat/map-sum-swap [U]) A B F is js))

;; ((p*q)*r) ~ ((p*r)*q)
(defn- reorder [p q r]
  (equiv-trans (rmul (rmul p q) r) (rmul p (rmul q r)) (rmul (rmul p r) q)
               (mul-assoc p q r)
               (equiv-trans (rmul p (rmul q r)) (rmul p (rmul r q)) (rmul (rmul p r) q)
                            (mul-respects p p (rmul q r) (rmul r q) (equiv-refl p) (mul-comm q r))
                            (equiv-sym (rmul (rmul p r) q) (rmul p (rmul r q)) (mul-assoc p r q)))))

(def gap-decomposition-spec
  {:name 'nnrat/lp-gap-decomposition :universes ['u]
   :type (function/forall
          [['RowT type-u] ['ColT type-u]
           ['A (arrow 'RowT (arrow 'ColT nnrat))]
           ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
           ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
           ['s (arrow 'RowT nnrat)] ['r (arrow 'ColT nnrat)]
           ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
           ['hp (function/forall [['i 'RowT]]
                                 (equiv (radd (map-sum 'ColT (lam 'j 'ColT (rmul (app (app 'A 'i) 'j) (app 'x 'j))) 'cols)
                                              (app 's 'i))
                                        (app 'b 'i)))]
           ['hd (function/forall [['j 'ColT]]
                                 (equiv (radd (app 'c 'j) (app 'r 'j))
                                        (map-sum 'RowT (lam 'i 'RowT (rmul (app (app 'A 'i) 'j) (app 'y 'i))) 'rows)))]]
          (equiv (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows)
                 (radd (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols)
                       (radd (map-sum 'ColT (lam 'j 'ColT (rmul (app 'r 'j) (app 'x 'j))) 'cols)
                             (map-sum 'RowT (lam 'i 'RowT (rmul (app 's 'i) (app 'y 'i))) 'rows)))))
   :value
   (function/lam
    [['RowT type-u] ['ColT type-u]
     ['A (arrow 'RowT (arrow 'ColT nnrat))]
     ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
     ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
     ['s (arrow 'RowT nnrat)] ['r (arrow 'ColT nnrat)]
     ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
     ['hp (function/forall [['i 'RowT]]
                           (equiv (radd (map-sum 'ColT (lam 'j 'ColT (rmul (app (app 'A 'i) 'j) (app 'x 'j))) 'cols)
                                        (app 's 'i))
                                  (app 'b 'i)))]
     ['hd (function/forall [['j 'ColT]]
                           (equiv (radd (app 'c 'j) (app 'r 'j))
                                  (map-sum 'RowT (lam 'i 'RowT (rmul (app (app 'A 'i) 'j) (app 'y 'i))) 'rows)))]]
    (let [Aij (fn [i j] (app (app 'A i) j))
          Ax  (fn [i] (map-sum 'ColT (lam 'j 'ColT (rmul (Aij i 'j) (app 'x 'j))) 'cols))
          ATy (fn [j] (map-sum 'RowT (lam 'i 'RowT (rmul (Aij 'i j) (app 'y 'i))) 'rows))
          by (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows)
          cx (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols)
          SR (map-sum 'ColT (lam 'j 'ColT (rmul (app 'r 'j) (app 'x 'j))) 'cols)
          SS (map-sum 'RowT (lam 'i 'RowT (rmul (app 's 'i) (app 'y 'i))) 'rows)
          P  (map-sum 'RowT (lam 'i 'RowT (rmul (Ax 'i) (app 'y 'i))) 'rows)
          Q  (map-sum 'ColT (lam 'j 'ColT (rmul (ATy 'j) (app 'x 'j))) 'cols)

          ;; ---- Step A : by ~ P + SS ----
          by-map  (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i)))
          phi-map (lam 'i 'RowT (radd (rmul (Ax 'i) (app 'y 'i)) (rmul (app 's 'i) (app 'y 'i))))
          pA (lam 'i 'RowT
                  (equiv-trans (rmul (app 'b 'i) (app 'y 'i))
                               (rmul (radd (Ax 'i) (app 's 'i)) (app 'y 'i))
                               (radd (rmul (Ax 'i) (app 'y 'i)) (rmul (app 's 'i) (app 'y 'i)))
                               (mul-respects (app 'b 'i) (radd (Ax 'i) (app 's 'i)) (app 'y 'i) (app 'y 'i)
                                             (equiv-sym (radd (Ax 'i) (app 's 'i)) (app 'b 'i) (app 'hp 'i))
                                             (equiv-refl (app 'y 'i)))
                               (dist-right (Ax 'i) (app 's 'i) (app 'y 'i))))
          respA (map-sum-respects 'RowT by-map phi-map pA 'rows)
          addA  (map-sum-add 'RowT (lam 'i 'RowT (rmul (Ax 'i) (app 'y 'i)))
                             (lam 'i 'RowT (rmul (app 's 'i) (app 'y 'i))) 'rows)
          byA (equiv-trans by (map-sum 'RowT phi-map 'rows) (radd P SS) respA addA)

          ;; ---- Step B : P ~ Q (scale-right, Fubini, reorder, scale-right back) ----
          P-map (lam 'i 'RowT (rmul (Ax 'i) (app 'y 'i)))
          DSP-imap (fn [i] (lam 'j 'ColT (rmul (rmul (Aij i 'j) (app 'x 'j)) (app 'y i))))
          DSP-map  (lam 'i 'RowT (map-sum 'ColT (DSP-imap 'i) 'cols))
          DSP (map-sum 'RowT DSP-map 'rows)
          scaleP (lam 'i 'RowT
                      (scale-right 'ColT (lam 'j 'ColT (rmul (Aij 'i 'j) (app 'x 'j))) (app 'y 'i) 'cols))
          respP (map-sum-respects 'RowT P-map DSP-map scaleP 'rows)
          Ffub-P (lam 'i 'RowT (lam 'j 'ColT (rmul (rmul (Aij 'i 'j) (app 'x 'j)) (app 'y 'i))))
          fubP (swap 'RowT 'ColT Ffub-P 'rows 'cols)
          DSP2-jmap (fn [j] (lam 'i 'RowT (rmul (rmul (Aij 'i j) (app 'x j)) (app 'y 'i))))
          DSP2-map (lam 'j 'ColT (map-sum 'RowT (DSP2-jmap 'j) 'rows))
          DSP2 (map-sum 'ColT DSP2-map 'cols)
          DSQ-jmap (fn [j] (lam 'i 'RowT (rmul (rmul (Aij 'i j) (app 'y 'i)) (app 'x j))))
          DSQ-map (lam 'j 'ColT (map-sum 'RowT (DSQ-jmap 'j) 'rows))
          DSQ (map-sum 'ColT DSQ-map 'cols)
          respReorder (map-sum-respects 'ColT DSP2-map DSQ-map
                                        (lam 'j 'ColT
                                             (map-sum-respects 'RowT (DSP2-jmap 'j) (DSQ-jmap 'j)
                                                               (lam 'i 'RowT (reorder (Aij 'i 'j) (app 'x 'j) (app 'y 'i)))
                                                               'rows))
                                        'cols)
          scaleQ (lam 'j 'ColT
                      (equiv-sym (rmul (ATy 'j) (app 'x 'j))
                                 (map-sum 'RowT (DSQ-jmap 'j) 'rows)
                                 (scale-right 'RowT (lam 'i 'RowT (rmul (Aij 'i 'j) (app 'y 'i))) (app 'x 'j) 'rows)))
          Q-map (lam 'j 'ColT (rmul (ATy 'j) (app 'x 'j)))
          respQ (map-sum-respects 'ColT DSQ-map Q-map scaleQ 'cols)
          Bpf (equiv-trans P DSP Q respP
                           (equiv-trans DSP DSP2 Q fubP
                                        (equiv-trans DSP2 DSQ Q respReorder respQ)))

          ;; ---- Step C : Q ~ cx + SR ----
          psi-map (lam 'j 'ColT (radd (rmul (app 'c 'j) (app 'x 'j)) (rmul (app 'r 'j) (app 'x 'j))))
          pC (lam 'j 'ColT
                  (equiv-trans (rmul (ATy 'j) (app 'x 'j))
                               (rmul (radd (app 'c 'j) (app 'r 'j)) (app 'x 'j))
                               (radd (rmul (app 'c 'j) (app 'x 'j)) (rmul (app 'r 'j) (app 'x 'j)))
                               (mul-respects (ATy 'j) (radd (app 'c 'j) (app 'r 'j)) (app 'x 'j) (app 'x 'j)
                                             (equiv-sym (radd (app 'c 'j) (app 'r 'j)) (ATy 'j) (app 'hd 'j))
                                             (equiv-refl (app 'x 'j)))
                               (dist-right (app 'c 'j) (app 'r 'j) (app 'x 'j))))
          respC (map-sum-respects 'ColT Q-map psi-map pC 'cols)
          addC (map-sum-add 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j)))
                            (lam 'j 'ColT (rmul (app 'r 'j) (app 'x 'j))) 'cols)
          Cpf (equiv-trans Q (map-sum 'ColT psi-map 'cols) (radd cx SR) respC addC)]

      ;; by ~ (P+SS) ~ (Q+SS) ~ ((cx+SR)+SS) ~ (cx+(SR+SS))
      (equiv-trans by (radd P SS) (radd cx (radd SR SS))
                   byA
                   (equiv-trans (radd P SS) (radd Q SS) (radd cx (radd SR SS))
                                (add-respects P Q SS SS Bpf (equiv-refl SS))
                                (equiv-trans (radd Q SS) (radd (radd cx SR) SS) (radd cx (radd SR SS))
                                             (add-respects Q (radd cx SR) SS SS Cpf (equiv-refl SS))
                                             (add-assoc cx SR SS))))))})

(def definition-specs [])
(def theorem-specs [gap-decomposition-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      lp/extend-environment
      (support/extend-with :nnrat-lp-gap
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
