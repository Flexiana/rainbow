(ns rainbow.algorithms.proofs.graph.walk-concat
  "CONCATENATING WALKS, for the Floyd-Warshall invariant. A
  walk x of a arcs ending where a walk y of b arcs starts (x a = y 0) joins into

     concat x a y = fun t. if t <= a then x t else y (t - a)          (b + a arcs)

     signed/walk-concat : x a = y 0 ->
       concat 0 = x 0 /\\ concat (b + a) = y b /\\ walk-length (concat, b + a) ~ walk-length (x, a) + walk-length (y, b)
     nat/walk-concat-range : x and y within n  ->  concat within n

  The length splits with signed/expr-sum-value-append. The first a arcs are x's, and the
  rest are y's because concat t = y (t - a) from a on (nat/walk-concat-tail, using x a = y 0 at
  t = a and (i + a) - a = i)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.algorithms.proofs.graph.walk-cycle-cut :as cycle-cut]
            [rainbow.math.nat.monus :as monus]
            [rainbow.math.nat.at-most-cancellation :as at-most-cancellation]))

(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private weight-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- monus [a b] (app (function/const* 'nat/monus []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
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
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- decide [a b] (app (function/const* 'nat/decide-at-most []) a b))
(defn- equiv-of-eq
  "Eq a b |- a ~ b. The motive binder has a name no caller uses: a binder named y captured the walk y."
  [a b h] (subst-signed a b h (function/lam [['eq-target-value signed]] (sequiv a 'eq-target-value)) (equiv-refl a)))

(defn- arc-weights [W x] (function/lam [['t nat]] (app W (app x 't) (app x (succ 't)))))
(defn- walk-length [W x k] (expr-sum-value (arc-weights W x) k))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn concat-walk [x a y] (function/lam [['t nat]] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app y (monus 't a)) (app x 't) (decide 't a))))
(defn- concat-at [x a y t] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app y (monus t a)) (app x t) (decide t a)))

(def monus-shift-spec
  {:name 'nat/monus-after-add :universes []
   :type (function/forall [['i nat] ['a nat]] (eq-nat (monus (nadd 'i 'a) 'a) 'i))
   :value (function/lam
           [['i nat] ['a nat]]
           (subst-nat (nadd 'a 'i) (nadd 'i 'a) (app (function/const* 'nat/add-commutative []) 'a 'i)
                      (function/lam [['z nat]] (eq-nat (monus 'z 'a) 'i))
                      (app (function/const* 'nat/monus-add-cancel-left []) 'a 'i)))})

(def concat-head-spec
  {:name 'nat/walk-concat-head :universes []
   :type (function/forall [['x walk-type] ['a nat] ['y walk-type] ['t nat] ['ht (at-most 't 'a)]] (eq-nat (concat-at 'x 'a 'y 't) (app 'x 't)))
   :value (function/lam
           [['x walk-type] ['a nat] ['y walk-type] ['t nat] ['ht (at-most 't 'a)]]
           (subst-bool true-value (decide 't 'a) (bool-sym (decide 't 'a) true-value (app (function/const* 'nat/decide-at-most-true-complete []) 't 'a 'ht))
                       (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app 'y (monus 't 'a)) (app 'x 't) 'b) (app 'x 't)))
                       (nat-refl (app 'x 't))))})

(def concat-tail-spec
  {:name 'nat/walk-concat-tail :universes []
   :type (function/forall [['x walk-type] ['a nat] ['y walk-type] ['hj (eq-nat (app 'x 'a) (app 'y nat-zero))] ['i nat]]
                          (eq-nat (concat-at 'x 'a 'y (nadd 'i 'a)) (app 'y 'i)))
   :value
   (function/lam
    [['x walk-type] ['a nat] ['y walk-type] ['hj (eq-nat (app 'x 'a) (app 'y nat-zero))] ['i nat]]
    (let [t (nadd 'i 'a) goal (eq-nat (concat-at 'x 'a 'y t) (app 'y 'i))
          shift (app (function/const* 'nat/monus-after-add []) 'i 'a)                                 ; (i + a) - a = i
          y-shift (subst-nat (monus t 'a) 'i shift (function/lam [['z nat]] (eq-nat (app 'y (monus t 'a)) (app 'y 'z))) (nat-refl (app 'y (monus t 'a))))]
      (use-disj (eq-nat nat-zero 'i) (strict-below nat-zero 'i) goal
                (app (function/const* 'nat/at-most-split []) nat-zero 'i
                     (witness (function/lam [['e nat]] (eq-nat (nadd nat-zero 'e) 'i)) 'i (nat-refl 'i)))
                ;; i = 0: concat a = x a = y 0
                (function/lam
                 [['h0 (eq-nat nat-zero 'i)]]
                 (subst-nat nat-zero 'i 'h0 (function/lam [['z nat]] (eq-nat (concat-at 'x 'a 'y (nadd 'z 'a)) (app 'y 'z)))
                            (nat-trans (concat-at 'x 'a 'y 'a) (app 'x 'a) (app 'y nat-zero)
                                       (app (function/const* 'nat/walk-concat-head []) 'x 'a 'y 'a (at-most-refl 'a)) 'hj)))
                ;; i > 0: i + a > a, the decision is false
                (function/lam
                 [['hp (strict-below nat-zero 'i)]]
                 (let [not-le (function/lam [['hle (at-most t 'a)]]
                                            (app (function/const* 'nat/not-strictly-below-self []) 'a
                                                 (amt (succ 'a) t 'a
                                                      (app (function/const* 'nat/add-right-monotone []) 'a (succ nat-zero) 'i 'hp) 'hle)))]
                   (subst-bool false-value (decide t 'a)
                               (bool-sym (decide t 'a) false-value (app (function/const* 'nat/decide-at-most-false-complete []) t 'a not-le))
                               (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) (app 'y (monus t 'a)) (app 'x t) 'b) (app 'y 'i)))
                               y-shift))))))})

(defn- concat-binders []
  [['W weight-type] ['x walk-type] ['a nat] ['y walk-type] ['b nat] ['hj (eq-nat (app 'x 'a) (app 'y nat-zero))]])
(defn- concat-claim [W x a y b]
  (let [z (concat-walk x a y)]
    (conj* (eq-nat (app z nat-zero) (app x nat-zero))
           (conj* (eq-nat (app z (nadd b a)) (app y b))
                  (sequiv (walk-length W z (nadd b a)) (signed-add (walk-length W x a) (walk-length W y b)))))))

(def concat-spec
  {:name 'signed/walk-concat :universes []
   :type (function/forall (concat-binders) (concat-claim 'W 'x 'a 'y 'b))
   :value
   (function/lam
    (concat-binders)
    (let [z (concat-walk 'x 'a 'y) Gz (arc-weights 'W z) Gx (arc-weights 'W 'x) Gy (arc-weights 'W 'y)
          shifted (function/lam [['i nat]] (app Gz (nadd 'i 'a)))
          A (app (function/const* 'signed/expr-sum-value-append []) Gz 'a 'b)            ; len z (b+a) ~ len z a + sum shifted b
          head (fn [t ht] (app (function/const* 'nat/walk-concat-head []) 'x 'a 'y t ht))
          tail (fn [i] (app (function/const* 'nat/walk-concat-tail []) 'x 'a 'y 'hj i))
          pre-agree (function/lam
                     [['t nat] ['ht (strict-below 't 'a)]]
                     (let [e1 (head 't (amt 't (succ 't) 'a (at-most-succ 't) 'ht)) e2 (head (succ 't) 'ht)
                           lhs (app 'W (app z 't) (app z (succ 't)))
                           s1 (subst-nat (app z 't) (app 'x 't) e1 (function/lam [['q nat]] (eq-signed lhs (app 'W 'q (app z (succ 't)))))
                                         (app (function/const* 'equality/reflexive [type-level]) signed lhs))]
                       (subst-nat (app z (succ 't)) (app 'x (succ 't)) e2 (function/lam [['q nat]] (eq-signed lhs (app 'W (app 'x 't) 'q))) s1)))
          pre-eq (equiv-of-eq (expr-sum-value Gz 'a) (walk-length 'W 'x 'a) (app (function/const* 'signed/expr-sum-value-congruence-below []) Gz Gx 'a pre-agree))
          suf-agree (function/lam
                     [['i nat] ['hi (strict-below 'i 'b)]]
                     (let [e1 (tail 'i) e2 (tail (succ 'i))
                           ia (nadd 'i 'a) lhs (app 'W (app z ia) (app z (succ ia)))
                           s1 (subst-nat (app z ia) (app 'y 'i) e1 (function/lam [['q nat]] (eq-signed lhs (app 'W 'q (app z (succ ia)))))
                                         (app (function/const* 'equality/reflexive [type-level]) signed lhs))]
                       (subst-nat (app z (succ ia)) (app 'y (succ 'i)) e2 (function/lam [['q nat]] (eq-signed lhs (app 'W (app 'y 'i) 'q))) s1)))
          suf-eq (equiv-of-eq (expr-sum-value shifted 'b) (walk-length 'W 'y 'b) (app (function/const* 'signed/expr-sum-value-congruence-below []) shifted Gy 'b suf-agree))
          len-eq (equiv-trans (walk-length 'W z (nadd 'b 'a)) (signed-add (expr-sum-value Gz 'a) (expr-sum-value shifted 'b))
                              (signed-add (walk-length 'W 'x 'a) (walk-length 'W 'y 'b)) A
                              (app (function/const* 'signed/add-respects-equivalence []) (expr-sum-value Gz 'a) (walk-length 'W 'x 'a)
                                   (expr-sum-value shifted 'b) (walk-length 'W 'y 'b) pre-eq suf-eq))
          z0 (head nat-zero (witness (function/lam [['e nat]] (eq-nat (nadd nat-zero 'e) 'a)) 'a (nat-refl 'a)))
          zend (tail 'b)]
      (conjoin (eq-nat (app z nat-zero) (app 'x nat-zero))
               (conj* (eq-nat (app z (nadd 'b 'a)) (app 'y 'b)) (sequiv (walk-length 'W z (nadd 'b 'a)) (signed-add (walk-length 'W 'x 'a) (walk-length 'W 'y 'b))))
               z0
               (conjoin (eq-nat (app z (nadd 'b 'a)) (app 'y 'b)) (sequiv (walk-length 'W z (nadd 'b 'a)) (signed-add (walk-length 'W 'x 'a) (walk-length 'W 'y 'b)))
                        zend len-eq))))})

(def concat-range-spec
  {:name 'nat/walk-concat-range :universes []
   :type (function/forall [['n nat] ['x walk-type] ['a nat] ['y walk-type] ['b nat] ['hj (eq-nat (app 'x 'a) (app 'y nat-zero))]
                           ['hx (in-range 'n 'x 'a)] ['hy (in-range 'n 'y 'b)]]
                          (in-range 'n (concat-walk 'x 'a 'y) (nadd 'b 'a)))
   :value
   (function/lam
    [['n nat] ['x walk-type] ['a nat] ['y walk-type] ['b nat] ['hj (eq-nat (app 'x 'a) (app 'y nat-zero))]
     ['hx (in-range 'n 'x 'a)] ['hy (in-range 'n 'y 'b)]]
    (function/lam
     [['t nat] ['ht (at-most 't (nadd 'b 'a))]]
     (let [goal (strict-below (concat-at 'x 'a 'y 't) 'n)]
       (use-disj (at-most 'a 't) (strict-below 't 'a) goal
                 (app (function/const* 'nat/at-most-or-strict-below []) 't 'a)
                 ;; t >= a: t = a + e, so concat t = y e with e <= b
                 (function/lam
                  [['hge (at-most 'a 't)]]
                  (app 'hge goal
                       (function/lam
                        [['e nat] ['pe (eq-nat (nadd 'a 'e) 't)]]
                        (let [te (nat-trans (nadd 'e 'a) (nadd 'a 'e) 't (app (function/const* 'nat/add-commutative []) 'e 'a) 'pe)
                              ;; t <= b + a, t = a + e  |-  a + e <= a + b  |-  e <= b
                              ae-le (subst-nat 't (nadd 'a 'e) (nat-sym (nadd 'a 'e) 't 'pe) (function/lam [['q nat]] (at-most 'q (nadd 'b 'a))) 'ht)
                              ae-le2 (subst-nat (nadd 'b 'a) (nadd 'a 'b) (app (function/const* 'nat/add-commutative []) 'b 'a)
                                                (function/lam [['q nat]] (at-most (nadd 'a 'e) 'q)) ae-le)
                              e-le (app (function/const* 'nat/at-most-add-left-cancel []) 'e 'b 'a ae-le2)]
                          (subst-nat (app 'y 'e) (concat-at 'x 'a 'y 't)
                                     (nat-sym (concat-at 'x 'a 'y 't) (app 'y 'e)
                                              (subst-nat (nadd 'e 'a) 't te (function/lam [['q nat]] (eq-nat (concat-at 'x 'a 'y 'q) (app 'y 'e)))
                                                         (app (function/const* 'nat/walk-concat-tail []) 'x 'a 'y 'hj 'e)))
                                     (function/lam [['q nat]] (strict-below 'q 'n))
                                     (app 'hy 'e e-le))))))
                 ;; t < a: concat t = x t
                 (function/lam
                  [['hl (strict-below 't 'a)]]
                  (let [t-le (amt 't (succ 't) 'a (at-most-succ 't) 'hl)]
                    (subst-nat (app 'x 't) (concat-at 'x 'a 'y 't) (nat-sym (concat-at 'x 'a 'y 't) (app 'x 't) (app (function/const* 'nat/walk-concat-head []) 'x 'a 'y 't t-le))
                               (function/lam [['q nat]] (strict-below 'q 'n)) (app 'hx 't t-le))))))))})

(def theorem-specs [monus-shift-spec concat-head-spec concat-tail-spec concat-spec concat-range-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      cycle-cut/extend-environment
      monus/extend-environment
      at-most-cancellation/extend-environment
      (support/extend-with :walk-concat theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
