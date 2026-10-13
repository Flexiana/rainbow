(ns rainbow.algorithms.proofs.graph.walk-cycle-cut
  "CUTTING A CYCLE OUT OF A WALK, the step of the Bellman-Ford cycle-removal lemma. A walk x of k = c + (d + a) arcs that revisits a node,
  x (d + a) = x a, loses the closed segment x a .. x (d + a):

     cut x a d = fun t. if t <= a then x t else x (t + d)          (c + a arcs)

  If no closed walk is negative (signed/no-negative-cycles: every walk z of d arcs over nodes
  < n with z d = z 0 has length >= 0), the cut walk has the same ends and is no longer:

     signed/walk-cut-cycle :
       no-negative-cycles n W -> (forall t <= c + (d + a), x t < n) -> x (d + a) = x a ->
         (forall t <= c + a, cut t < n) /\\ cut 0 = x 0 /\\ cut (c + a) = x (c + (d + a))
         /\\ walk-length (cut, c + a) <= walk-length (x, c + (d + a))

  The lengths are split with signed/expr-sum-value-append into prefix (a arcs), cycle
  (d arcs) and suffix (c arcs). The prefixes agree because cut = x up to a. The suffixes agree term
  by term because cut t = x (t + d) from a on (nat/walk-cut-shifted) and (i + a) + d = i + (d + a).
  The cycle is the closed walk fun t. x (t + a), so it is >= 0."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sums.value-append :as append]
            [rainbow.algorithms.proofs.graph.bellman-ford-convergence-attained :as attained]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private weight-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- eq-bool [a b] (app (function/const* 'equality/Eq [type-level]) bool a b))
(defn- eq-signed [a b] (app (function/const* 'equality/Eq [type-level]) signed a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- nat-trans [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- subst-bool [x y h P px] (app (function/const* 'equality/substitution [type-level]) bool x y h P px))
(defn- subst-signed [x y h P px] (app (function/const* 'equality/substitution [type-level]) signed x y h P px))
(defn- bool-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) bool a b h))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- decide [a b] (app (function/const* 'nat/decide-at-most []) a b))
(defn- equiv-of-eq [a b h] (subst-signed a b h (function/lam [['y signed]] (sequiv a 'y)) (equiv-refl a)))

(defn- arc-weights [W x] (function/lam [['t nat]] (app W (app x 't) (app x (succ 't)))))
(defn- walk-length [W x k] (expr-sum-value (arc-weights W x) k))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn- cut [x a d] (function/lam [['t nat]] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app x (nadd 't d)) (app x 't) (decide 't a))))
(defn- cut-at [x a d t] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app x (nadd t d)) (app x t) (decide t a)))

(defn no-negative-cycles
  "every closed walk of d arcs over nodes below n has nonnegative length"
  [n W]
  (function/forall [['z walk-type] ['d nat] ['hz (in-range n 'z 'd)] ['hc (eq-nat (app 'z 'd) (app 'z nat-zero))]]
                   (sle szero (walk-length W 'z 'd))))

;; ---------------------------------------------------------------------------------------------
(def shift-arith-spec
  {:name 'nat/walk-shift-arith :universes []
   :type (function/forall [['i nat] ['a nat] ['d nat]] (eq-nat (nadd (nadd 'i 'a) 'd) (nadd 'i (nadd 'd 'a))))
   :value (function/lam
           [['i nat] ['a nat] ['d nat]]
           (nat-trans (nadd (nadd 'i 'a) 'd) (nadd 'i (nadd 'a 'd)) (nadd 'i (nadd 'd 'a))
                      (app (function/const* 'nat/add-associative []) 'i 'a 'd)
                      (subst-nat (nadd 'a 'd) (nadd 'd 'a) (app (function/const* 'nat/add-commutative []) 'a 'd)
                                 (function/lam [['z nat]] (eq-nat (nadd 'i (nadd 'a 'd)) (nadd 'i 'z)))
                                 (nat-refl (nadd 'i (nadd 'a 'd))))))})

(def cut-below-spec
  {:name 'nat/walk-cut-below :universes []
   :type (function/forall [['x walk-type] ['a nat] ['d nat] ['t nat] ['ht (at-most 't 'a)]] (eq-nat (cut-at 'x 'a 'd 't) (app 'x 't)))
   :value (function/lam
           [['x walk-type] ['a nat] ['d nat] ['t nat] ['ht (at-most 't 'a)]]
           (subst-bool true-value (decide 't 'a) (bool-sym (decide 't 'a) true-value (app (function/const* 'nat/decide-at-most-true-complete []) 't 'a 'ht))
                       (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app 'x (nadd 't 'd)) (app 'x 't) 'b) (app 'x 't)))
                       (nat-refl (app 'x 't))))})

(def cut-shifted-spec
  {:name 'nat/walk-cut-shifted :universes []
   :type (function/forall [['x walk-type] ['a nat] ['d nat] ['hrep (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'a))] ['t nat] ['ht (at-most 'a 't)]]
                          (eq-nat (cut-at 'x 'a 'd 't) (app 'x (nadd 't 'd))))
   :value (function/lam
           [['x walk-type] ['a nat] ['d nat] ['hrep (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'a))] ['t nat] ['ht (at-most 'a 't)]]
           (let [goal (eq-nat (cut-at 'x 'a 'd 't) (app 'x (nadd 't 'd)))]
             (use-disj (eq-nat 'a 't) (strict-below 'a 't) goal
                       (app (function/const* 'nat/at-most-split []) 'a 't 'ht)
                       ;; t = a: cut a = x a = x (d + a) = x (a + d)
                       (function/lam
                        [['he (eq-nat 'a 't)]]
                        (subst-nat 'a 't 'he (function/lam [['z nat]] (eq-nat (cut-at 'x 'a 'd 'z) (app 'x (nadd 'z 'd))))
                                   (nat-trans (cut-at 'x 'a 'd 'a) (app 'x 'a) (app 'x (nadd 'a 'd))
                                              (app (function/const* 'nat/walk-cut-below []) 'x 'a 'd 'a (at-most-refl 'a))
                                              (nat-trans (app 'x 'a) (app 'x (nadd 'd 'a)) (app 'x (nadd 'a 'd))
                                                         (nat-sym (app 'x (nadd 'd 'a)) (app 'x 'a) 'hrep)
                                                         (subst-nat (nadd 'd 'a) (nadd 'a 'd) (app (function/const* 'nat/add-commutative []) 'd 'a)
                                                                    (function/lam [['z nat]] (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'z)))
                                                                    (nat-refl (app 'x (nadd 'd 'a))))))))
                       ;; t > a: the decision is false
                       (function/lam
                        [['hl (strict-below 'a 't)]]
                        (let [not-le (function/lam [['hle (at-most 't 'a)]]
                                                   (app (function/const* 'nat/not-strictly-below-self []) 'a (amt (succ 'a) 't 'a 'hl 'hle)))]
                          (subst-bool false-value (decide 't 'a)
                                      (bool-sym (decide 't 'a) false-value (app (function/const* 'nat/decide-at-most-false-complete []) 't 'a not-le))
                                      (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app 'x (nadd 't 'd)) (app 'x 't) 'b) (app 'x (nadd 't 'd))))
                                      (nat-refl (app 'x (nadd 't 'd)))))))))})

;; ---------------------------------------------------------------------------------------------
(defn- len-binders []
  [['n nat] ['W weight-type] ['hneg (no-negative-cycles 'n 'W)] ['x walk-type] ['a nat] ['d nat] ['c nat]
   ['hin (in-range 'n 'x (nadd 'c (nadd 'd 'a)))] ['hrep (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'a))]])

(def cut-length-spec
  {:name 'signed/walk-cut-length :universes []
   :type (function/forall (len-binders)
                          (sle (walk-length 'W (cut 'x 'a 'd) (nadd 'c 'a)) (walk-length 'W 'x (nadd 'c (nadd 'd 'a)))))
   :value
   (function/lam
    (len-binders)
    (let [y (cut 'x 'a 'd) Gx (arc-weights 'W 'x) Gy (arc-weights 'W y) da (nadd 'd 'a)
          shifted (fn [G off] (function/lam [['i nat]] (app G (nadd 'i off))))
          app-lemma (fn [G off b] (app (function/const* 'signed/expr-sum-value-append []) G off b))
          px (expr-sum-value Gx 'a)                                   ; prefix of x
          cyc (expr-sum-value (shifted Gx 'a) 'd)                     ; the cycle
          sx (expr-sum-value (shifted Gx da) 'c)                      ; suffix of x
          sy (expr-sum-value (shifted Gy 'a) 'c)                      ; suffix of y
          lx (walk-length 'W 'x (nadd 'c da)) ly (walk-length 'W y (nadd 'c 'a))
          A1 (app-lemma Gx da 'c)                                     ; lx ~ len(x, d+a) + sx
          A2 (app-lemma Gx 'a 'd)                                     ; len(x, d+a) ~ px + cyc
          A3 (app-lemma Gy 'a 'c)                                     ; ly ~ len(y, a) + sy
          ;; prefixes agree: for t < a, y t = x t and y (t+1) = x (t+1)
          pre-agree (function/lam
                     [['t nat] ['ht (strict-below 't 'a)]]
                     (let [e1 (app (function/const* 'nat/walk-cut-below []) 'x 'a 'd 't (amt 't (succ 't) 'a (at-most-succ 't) 'ht))
                           e2 (app (function/const* 'nat/walk-cut-below []) 'x 'a 'd (succ 't) 'ht)
                           lhs (app 'W (app y 't) (app y (succ 't)))
                           s1 (subst-nat (app y 't) (app 'x 't) e1 (function/lam [['z nat]] (eq-signed lhs (app 'W 'z (app y (succ 't)))))
                                         (app (function/const* 'equality/reflexive [type-level]) signed lhs))]
                       (subst-nat (app y (succ 't)) (app 'x (succ 't)) e2 (function/lam [['z nat]] (eq-signed lhs (app 'W (app 'x 't) 'z))) s1)))
          pre-eq (equiv-of-eq (expr-sum-value Gy 'a) px (app (function/const* 'signed/expr-sum-value-congruence-below []) Gy Gx 'a pre-agree))
          ;; suffixes agree: y (i + a) = x (i + (d + a)), y (succ (i + a)) = x (succ (i + (d + a)))
          suf-agree (function/lam
                     [['i nat] ['hi (strict-below 'i 'c)]]
                     (let [ia (nadd 'i 'a)
                           arith (app (function/const* 'nat/walk-shift-arith []) 'i 'a 'd)                     ; (i+a)+d = i+(d+a)
                           a-le (app (function/const* 'nat/at-most-add-left []) 'a 'i)                           ; a <= i + a
                           e1 (nat-trans (app y ia) (app 'x (nadd ia 'd)) (app 'x (nadd 'i da))
                                         (app (function/const* 'nat/walk-cut-shifted []) 'x 'a 'd 'hrep ia a-le)
                                         (subst-nat (nadd ia 'd) (nadd 'i da) arith (function/lam [['z nat]] (eq-nat (app 'x (nadd ia 'd)) (app 'x 'z))) (nat-refl (app 'x (nadd ia 'd)))))
                           e2 (nat-trans (app y (succ ia)) (app 'x (nadd (succ ia) 'd)) (app 'x (succ (nadd 'i da)))
                                         (app (function/const* 'nat/walk-cut-shifted []) 'x 'a 'd 'hrep (succ ia) (amt 'a ia (succ ia) a-le (at-most-succ ia)))
                                         (subst-nat (nadd ia 'd) (nadd 'i da) arith (function/lam [['z nat]] (eq-nat (app 'x (succ (nadd ia 'd))) (app 'x (succ 'z)))) (nat-refl (app 'x (succ (nadd ia 'd))))))
                           lhs (app 'W (app y ia) (app y (succ ia)))
                           s1 (subst-nat (app y ia) (app 'x (nadd 'i da)) e1 (function/lam [['z nat]] (eq-signed lhs (app 'W 'z (app y (succ ia)))))
                                         (app (function/const* 'equality/reflexive [type-level]) signed lhs))]
                       (subst-nat (app y (succ ia)) (app 'x (succ (nadd 'i da))) e2 (function/lam [['z nat]] (eq-signed lhs (app 'W (app 'x (nadd 'i da)) 'z))) s1)))
          suf-eq (equiv-of-eq sy sx (app (function/const* 'signed/expr-sum-value-congruence-below []) (shifted Gy 'a) (shifted Gx da) 'c suf-agree))
          ;; the cycle is the closed walk fun t. x (t + a)
          z (function/lam [['t nat]] (app 'x (nadd 't 'a)))
          z-range (function/lam [['t nat] ['ht (at-most 't 'd)]]
                                (app 'hin (nadd 't 'a)
                                     (amt (nadd 't 'a) da (nadd 'c da)
                                          (app (function/const* 'nat/add-right-monotone []) 'a 't 'd 'ht)
                                          (app (function/const* 'nat/at-most-add-left []) da 'c))))
          cyc-nonneg (app 'hneg z 'd z-range 'hrep)
          ;; ly ~ px + sx <= (px + cyc) + sx ~ lx
          ly-eq (equiv-trans ly (signed-add (expr-sum-value Gy 'a) sy) (signed-add px sx) A3
                             (app (function/const* 'signed/add-respects-equivalence []) (expr-sum-value Gy 'a) px sy sx pre-eq suf-eq))
          px-le (le-respects (signed-add px szero) px (signed-add px cyc) (signed-add px cyc)
                             (app (function/const* 'signed/add-zero-right []) px) (equiv-refl (signed-add px cyc))
                             (app (function/const* 'signed/add-left-monotone []) szero cyc px cyc-nonneg))
          lx-eq (equiv-trans (signed-add (signed-add px cyc) sx) (signed-add (expr-sum-value Gx da) sx) lx
                             (app (function/const* 'signed/add-respects-equivalence []) (signed-add px cyc) (expr-sum-value Gx da) sx sx
                                  (equiv-sym (expr-sum-value Gx da) (signed-add px cyc) A2) (equiv-refl sx))
                             (equiv-sym lx (signed-add (expr-sum-value Gx da) sx) A1))]
      (le-respects (signed-add px sx) ly (signed-add (signed-add px cyc) sx) lx
                   (equiv-sym ly (signed-add px sx) ly-eq) lx-eq
                   (app (function/const* 'signed/add-right-monotone []) px (signed-add px cyc) sx px-le))))})

(def cut-range-spec
  {:name 'nat/walk-cut-range :universes []
   :type (function/forall [['n nat] ['x walk-type] ['a nat] ['d nat] ['c nat]
                           ['hin (in-range 'n 'x (nadd 'c (nadd 'd 'a)))] ['hrep (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'a))]]
                          (in-range 'n (cut 'x 'a 'd) (nadd 'c 'a)))
   :value
   (function/lam
    [['n nat] ['x walk-type] ['a nat] ['d nat] ['c nat]
     ['hin (in-range 'n 'x (nadd 'c (nadd 'd 'a)))] ['hrep (eq-nat (app 'x (nadd 'd 'a)) (app 'x 'a))]]
    (function/lam
     [['t nat] ['ht (at-most 't (nadd 'c 'a))]]
     (let [k (nadd 'c (nadd 'd 'a)) goal (strict-below (cut-at 'x 'a 'd 't) 'n)]
       (use-disj (at-most 'a 't) (strict-below 't 'a) goal
                 (app (function/const* 'nat/at-most-or-strict-below []) 't 'a)
                 ;; t >= a: cut t = x (t + d), and t + d <= (c + a) + d = c + (d + a)
                 (function/lam
                  [['hge (at-most 'a 't)]]
                  (let [td-le (amt (nadd 't 'd) (nadd (nadd 'c 'a) 'd) k
                                   (app (function/const* 'nat/add-right-monotone []) 'd 't (nadd 'c 'a) 'ht)
                                   (subst-nat (nadd (nadd 'c 'a) 'd) k (app (function/const* 'nat/walk-shift-arith []) 'c 'a 'd)
                                              (function/lam [['z nat]] (at-most (nadd (nadd 'c 'a) 'd) 'z)) (at-most-refl (nadd (nadd 'c 'a) 'd))))]
                    (subst-nat (app 'x (nadd 't 'd)) (cut-at 'x 'a 'd 't)
                               (nat-sym (cut-at 'x 'a 'd 't) (app 'x (nadd 't 'd)) (app (function/const* 'nat/walk-cut-shifted []) 'x 'a 'd 'hrep 't 'hge))
                               (function/lam [['z nat]] (strict-below 'z 'n)) (app 'hin (nadd 't 'd) td-le))))
                 ;; t < a: cut t = x t, and t <= a <= k
                 (function/lam
                  [['hl (strict-below 't 'a)]]
                  (let [t-le-a (amt 't (succ 't) 'a (at-most-succ 't) 'hl)
                        a-le-k (amt 'a (nadd 'd 'a) k (app (function/const* 'nat/at-most-add-left []) 'a 'd) (app (function/const* 'nat/at-most-add-left []) (nadd 'd 'a) 'c))]
                    (subst-nat (app 'x 't) (cut-at 'x 'a 'd 't)
                               (nat-sym (cut-at 'x 'a 'd 't) (app 'x 't) (app (function/const* 'nat/walk-cut-below []) 'x 'a 'd 't t-le-a))
                               (function/lam [['z nat]] (strict-below 'z 'n)) (app 'hin 't (amt 't 'a k t-le-a a-le-k)))))))))})

(def theorem-specs [shift-arith-spec cut-below-spec cut-shifted-spec cut-length-spec cut-range-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.graph.bellman-ford-convergence-attained rainbow.math.sums.value-append])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :walk-cycle-cut theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.graph.walk-cycle-cut))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
