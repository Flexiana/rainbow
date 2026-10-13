(ns rainbow.math.nat.pigeonhole
  "THE PIGEONHOLE PRINCIPLE ON NAT, constructively. n + 1 values below n repeat one:

     nat/pigeonhole :
       forall n f, (forall t <= n, f t < n) -> exists a b, a < b /\\ b <= n /\\ f a = f b

  with its supports:
     nat/trichotomy        : a < b \\/ a = b \\/ b < a
     nat/bounded-search    : (exists t <= n, f t = c) \\/ (forall t <= n, f t = c -> False)

  Pigeonhole is by induction on n. Let c = f(n+1). If some t <= n has f t = c, the pair is
  (t, n+1). Otherwise squeeze the top value into c: g t = if f t < n then f t else c. Then every
  g t < n: when f t is not below n it is n, and c is not n because otherwise f t = n = c. The
  induction hypothesis gives a < b <= n with g a = g b. In each of the four cases of the two
  decisions, f a = f b follows directly or the mixed case would make f a or f b equal to c.
  Consumer: the Bellman-Ford cycle-removal lemma (a walk of >= n arcs over n nodes repeats a
  node)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.rational.signed.decide-completeness :as decide-completeness]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(def ^:private fn-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- eq-bool [a b] (app (function/const* 'equality/Eq [type-level]) bool a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- bool-refl [a] (app (function/const* 'equality/reflexive [type-level]) bool a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- nat-trans [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- subst-bool [x y h P px] (app (function/const* 'equality/substitution [type-level]) bool x y h P px))
(defn- bool-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) bool a b h))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- falsity [] (function/const* 'proposition/falsity []))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- exists-nat [pred] (proposition/existence type-level nat pred))
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))
(defn- decide [a b] (app (function/const* 'nat/decide-at-most []) a b))
(defn- not* [P] (function/arrow P (falsity)))

(defn- self-below-absurd
  "b < b |- False"
  [b h] (app (function/const* 'nat/not-strictly-below-self []) b h))
(defn- below-zero-absurd [i hi P]
  (app hi P (function/lam [['e nat] ['pf (eq-nat (nadd (succ i) 'e) nat-zero)]]
                          (explode P (app (function/const* 'nat/zero-not-successor []) (nadd i 'e) (nat-sym (succ (nadd i 'e)) nat-zero 'pf))))))
(defn- le-of-below-succ [t k h]
  (app h (at-most t k)
       (function/lam [['e nat] ['pf (eq-nat (nadd (succ t) 'e) (succ k))]]
                     (witness (function/lam [['e2 nat]] (eq-nat (nadd t 'e2) k)) 'e
                              (app (function/const* 'nat/successor-injective []) (nadd t 'e) k 'pf)))))
(defn- zero-of-le-zero
  "t <= 0 |- t = 0"
  [t h]
  (use-disj (eq-nat t nat-zero) (strict-below t nat-zero) (eq-nat t nat-zero)
            (app (function/const* 'nat/at-most-split []) t nat-zero h)
            (function/lam [['he (eq-nat t nat-zero)]] 'he)
            (function/lam [['hl (strict-below t nat-zero)]] (below-zero-absurd t 'hl (eq-nat t nat-zero)))))
(defn- below-succ-of-le [t k h] (app (function/const* 'nat/successor-monotone []) t k h))

;; ---------------------------------------------------------------------------------------------
(defn- tri-prop [a b] (disj* (strict-below a b) (disj* (eq-nat a b) (strict-below b a))))
(def trichotomy-spec
  {:name 'nat/trichotomy :universes []
   :type (function/forall [['a nat] ['b nat]] (tri-prop 'a 'b))
   :value (function/lam
           [['a nat] ['b nat]]
           (use-disj (at-most 'b 'a) (strict-below 'a 'b) (tri-prop 'a 'b)
                     (app (function/const* 'nat/at-most-or-strict-below []) 'a 'b)
                     (function/lam [['hle (at-most 'b 'a)]]
                                   (use-disj (eq-nat 'b 'a) (strict-below 'b 'a) (tri-prop 'a 'b)
                                             (app (function/const* 'nat/at-most-split []) 'b 'a 'hle)
                                             (function/lam [['he (eq-nat 'b 'a)]]
                                                           (right-disj (strict-below 'a 'b) (disj* (eq-nat 'a 'b) (strict-below 'b 'a))
                                                                       (left-disj (eq-nat 'a 'b) (strict-below 'b 'a) (nat-sym 'b 'a 'he))))
                                             (function/lam [['hl (strict-below 'b 'a)]]
                                                           (right-disj (strict-below 'a 'b) (disj* (eq-nat 'a 'b) (strict-below 'b 'a))
                                                                       (right-disj (eq-nat 'a 'b) (strict-below 'b 'a) 'hl)))))
                     (function/lam [['hl (strict-below 'a 'b)]]
                                   (left-disj (strict-below 'a 'b) (disj* (eq-nat 'a 'b) (strict-below 'b 'a)) 'hl))))})

(defn- eq-or-not
  "a = b \\/ (a = b -> False), from trichotomy"
  [a b]
  (let [goal (disj* (eq-nat a b) (not* (eq-nat a b)))
        ne-of-lt (fn [lt-ab] (function/lam [['he (eq-nat a b)]]
                                           (self-below-absurd b (subst-nat a b 'he (function/lam [['z nat]] (strict-below 'z b)) lt-ab))))
        ne-of-gt (fn [lt-ba] (function/lam [['he (eq-nat a b)]]
                                           (self-below-absurd b (subst-nat a b 'he (function/lam [['z nat]] (strict-below b 'z)) lt-ba))))]
    (use-disj (strict-below a b) (disj* (eq-nat a b) (strict-below b a)) goal (app (function/const* 'nat/trichotomy []) a b)
              (function/lam [['h (strict-below a b)]] (right-disj (eq-nat a b) (not* (eq-nat a b)) (ne-of-lt 'h)))
              (function/lam [['h (disj* (eq-nat a b) (strict-below b a))]]
                            (use-disj (eq-nat a b) (strict-below b a) goal 'h
                                      (function/lam [['he (eq-nat a b)]] (left-disj (eq-nat a b) (not* (eq-nat a b)) 'he))
                                      (function/lam [['hl (strict-below b a)]] (right-disj (eq-nat a b) (not* (eq-nat a b)) (ne-of-gt 'hl))))))))

;; ---------------------------------------------------------------------------------------------
(defn- found [f c n] (exists-nat (function/lam [['t nat]] (conj* (at-most 't n) (eq-nat (app f 't) c)))))
(defn- none [f c n] (function/forall [['t nat] ['ht (at-most 't n)]] (not* (eq-nat (app f 't) c))))
(defn- search-prop [f c n] (disj* (found f c n) (none f c n)))

(def bounded-search-spec
  {:name 'nat/bounded-search :universes []
   :type (function/forall [['f fn-type] ['c nat] ['n nat]] (search-prop 'f 'c 'n))
   :value
   (function/lam
    [['f fn-type] ['c nat] ['n nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['nn nat]] (search-prop 'f 'c 'nn))
         (use-disj (eq-nat (app 'f nat-zero) 'c) (not* (eq-nat (app 'f nat-zero) 'c)) (search-prop 'f 'c nat-zero)
                   (eq-or-not (app 'f nat-zero) 'c)
                   (function/lam [['he (eq-nat (app 'f nat-zero) 'c)]]
                                 (left-disj (found 'f 'c nat-zero) (none 'f 'c nat-zero)
                                            (witness (function/lam [['t nat]] (conj* (at-most 't nat-zero) (eq-nat (app 'f 't) 'c))) nat-zero
                                                     (conjoin (at-most nat-zero nat-zero) (eq-nat (app 'f nat-zero) 'c) (at-most-refl nat-zero) 'he))))
                   (function/lam [['hn (not* (eq-nat (app 'f nat-zero) 'c))]]
                                 (right-disj (found 'f 'c nat-zero) (none 'f 'c nat-zero)
                                             (function/lam [['t nat] ['ht (at-most 't nat-zero)] ['he (eq-nat (app 'f 't) 'c)]]
                                                           (app 'hn (subst-nat 't nat-zero (zero-of-le-zero 't 'ht)
                                                                               (function/lam [['z nat]] (eq-nat (app 'f 'z) 'c)) 'he))))))
         (function/lam
          [['n nat] ['ih (search-prop 'f 'c 'n)]]
          (let [n1 (succ 'n) goal (search-prop 'f 'c n1)
                P1 (function/lam [['t nat]] (conj* (at-most 't n1) (eq-nat (app 'f 't) 'c)))
                P0 (function/lam [['t nat]] (conj* (at-most 't 'n) (eq-nat (app 'f 't) 'c)))]
            (use-disj (found 'f 'c 'n) (none 'f 'c 'n) goal 'ih
                      (function/lam [['hf (found 'f 'c 'n)]]
                                    (left-disj (found 'f 'c n1) (none 'f 'c n1)
                                               (app 'hf (found 'f 'c n1)
                                                    (function/lam [['t nat] ['pf (app P0 't)]]
                                                                  (witness P1 't (conjoin (at-most 't n1) (eq-nat (app 'f 't) 'c)
                                                                                          (amt 't 'n n1 (pleft (at-most 't 'n) (eq-nat (app 'f 't) 'c) 'pf) (at-most-succ 'n))
                                                                                          (pright (at-most 't 'n) (eq-nat (app 'f 't) 'c) 'pf)))))))
                      (function/lam
                       [['hn (none 'f 'c 'n)]]
                       (use-disj (eq-nat (app 'f n1) 'c) (not* (eq-nat (app 'f n1) 'c)) goal (eq-or-not (app 'f n1) 'c)
                                 (function/lam [['he (eq-nat (app 'f n1) 'c)]]
                                               (left-disj (found 'f 'c n1) (none 'f 'c n1)
                                                          (witness P1 n1 (conjoin (at-most n1 n1) (eq-nat (app 'f n1) 'c) (at-most-refl n1) 'he))))
                                 (function/lam [['hne (not* (eq-nat (app 'f n1) 'c))]]
                                               (right-disj (found 'f 'c n1) (none 'f 'c n1)
                                                           (function/lam
                                                            [['t nat] ['ht (at-most 't n1)]]
                                                            (use-disj (eq-nat 't n1) (strict-below 't n1) (not* (eq-nat (app 'f 't) 'c))
                                                                      (app (function/const* 'nat/at-most-split []) 't n1 'ht)
                                                                      (function/lam [['he (eq-nat 't n1)]]
                                                                                    (subst-nat n1 't (nat-sym 't n1 'he) (function/lam [['z nat]] (not* (eq-nat (app 'f 'z) 'c))) 'hne))
                                                                      (function/lam [['hl (strict-below 't n1)]]
                                                                                    (app 'hn 't (le-of-below-succ 't 'n 'hl))))))))))))
         'n))})

;; ---------------------------------------------------------------------------------------------
(defn- repeat-prop [f n]
  (exists-nat (function/lam [['a nat]]
                            (exists-nat (function/lam [['b nat]]
                                                      (conj* (strict-below 'a 'b) (conj* (at-most 'b n) (eq-nat (app f 'a) (app f 'b)))))))))
(defn- bounded-into [f n] (function/forall [['t nat] ['ht (at-most 't n)]] (strict-below (app f 't) n)))
(defn- claim [n] (function/forall [['f fn-type] ['hf (bounded-into 'f n)]] (repeat-prop 'f n)))

(defn- make-repeat [f n a b hab hbn heq]
  (witness (function/lam [['a2 nat]] (exists-nat (function/lam [['b2 nat]] (conj* (strict-below 'a2 'b2) (conj* (at-most 'b2 n) (eq-nat (app f 'a2) (app f 'b2)))))))
           a
           (witness (function/lam [['b2 nat]] (conj* (strict-below a 'b2) (conj* (at-most 'b2 n) (eq-nat (app f a) (app f 'b2)))))
                    b
                    (conjoin (strict-below a b) (conj* (at-most b n) (eq-nat (app f a) (app f b))) hab
                             (conjoin (at-most b n) (eq-nat (app f a) (app f b)) hbn heq)))))

(defn- g-of [f n c] (function/lam [['t nat]] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) c (app f 't) (decide (succ (app f 't)) n))))
(defn- g-at [f n c t] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) c (app f t) (decide (succ (app f t)) n)))

(defn- on-decision
  "case analysis on decide (succ (f t)) n with its equation, binding the equation as `hname`
   (distinct names for nested splits: a shared name is captured by the inner binder)"
  ([f n t goal on-true on-false] (on-decision f n t goal on-true on-false (symbol (str "hd-" t))))
  ([f n t goal on-true on-false hname]
   (let [d (decide (succ (app f t)) n)]
     (app (app (function/const* 'data/Bool.rec [prop-level])
               (function/lam [['ch bool]] (function/forall [[hname (eq-bool d 'ch)]] goal))
               (function/lam [[hname (eq-bool d false-value)]] (on-false hname))
               (function/lam [[hname (eq-bool d true-value)]] (on-true hname))
               d)
          (bool-refl d)))))

(defn- g-when [f n c t hd b result]
  "decide = b |- g t = result (result is f t for true, c for false)"
  (subst-bool b (decide (succ (app f t)) n) (bool-sym (decide (succ (app f t)) n) b hd)
              (function/lam [['bb bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) c (app f t) 'bb) result))
              (nat-refl result)))

(def pigeonhole-spec
  {:name 'nat/pigeonhole :universes []
   :type (function/forall [['n nat]] (claim 'n))
   :value
   (function/lam
    [['n nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['nn nat]] (claim 'nn))
         ;; n = 0: f 0 < 0 is impossible
         (function/lam [['f fn-type] ['hf (bounded-into 'f nat-zero)]]
                       (below-zero-absurd (app 'f nat-zero) (app 'hf nat-zero (at-most-refl nat-zero)) (repeat-prop 'f nat-zero)))
         (function/lam
          [['n nat] ['ih (claim 'n)] ['f fn-type] ['hf (bounded-into 'f (succ 'n))]]
          (let [n1 (succ 'n) c (app 'f n1) goal (repeat-prop 'f n1)
                P0 (function/lam [['t nat]] (conj* (at-most 't 'n) (eq-nat (app 'f 't) c)))]
            (use-disj (found 'f c 'n) (none 'f c 'n) goal (app (function/const* 'nat/bounded-search []) 'f c 'n)
                      ;; some t <= n hits c: the pair (t, n + 1)
                      (function/lam
                       [['hfd (found 'f c 'n)]]
                       (app 'hfd goal
                            (function/lam [['t nat] ['pf (app P0 't)]]
                                          (make-repeat 'f n1 't n1
                                                       (below-succ-of-le 't 'n (pleft (at-most 't 'n) (eq-nat (app 'f 't) c) 'pf))
                                                       (at-most-refl n1)
                                                       (pright (at-most 't 'n) (eq-nat (app 'f 't) c) 'pf)))))
                      ;; no t <= n hits c: squeeze and recurse
                      (function/lam
                       [['hno (none 'f c 'n)]]
                       (let [g (g-of 'f 'n c)
                             ;; f t < n + 1 and not f t < n  |-  f t = n
                             top (fn [t t-le hd]
                                   (let [ft (app 'f t)
                                         ft-le (le-of-below-succ ft 'n (app 'hf t (amt t 'n n1 t-le (at-most-succ 'n))))
                                         not-below (app (function/const* 'nat/decide-at-most-false-sound []) (succ ft) 'n hd)]
                                     (use-disj (eq-nat ft 'n) (strict-below ft 'n) (eq-nat ft 'n)
                                               (app (function/const* 'nat/at-most-split []) ft 'n ft-le)
                                               (function/lam [['he (eq-nat ft 'n)]] 'he)
                                               (function/lam [['hl (strict-below ft 'n)]] (explode (eq-nat ft 'n) (app not-below 'hl))))))
                             ;; c < n: c <= n, and c = n would make the squeezed top equal c
                             c-le (le-of-below-succ c 'n (app 'hf n1 (at-most-refl n1)))
                             g-bound
                             (function/lam
                              [['t nat] ['ht (at-most 't 'n)]]
                              (on-decision 'f 'n 't (strict-below (g-at 'f 'n c 't) 'n)
                                           (fn [hd] (subst-nat (app 'f 't) (g-at 'f 'n c 't) (nat-sym (g-at 'f 'n c 't) (app 'f 't) (g-when 'f 'n c 't hd true-value (app 'f 't)))
                                                               (function/lam [['z nat]] (strict-below 'z 'n))
                                                               (app (function/const* 'nat/decide-at-most-true-sound []) (succ (app 'f 't)) 'n hd)))
                                           (fn [hd] (let [ft-n (top 't 'ht hd)
                                                          c-below (use-disj (eq-nat c 'n) (strict-below c 'n) (strict-below c 'n)
                                                                            (app (function/const* 'nat/at-most-split []) c 'n c-le)
                                                                            (function/lam [['hcn (eq-nat c 'n)]]
                                                                                          (explode (strict-below c 'n)
                                                                                                   (app 'hno 't 'ht (nat-trans (app 'f 't) 'n c ft-n (nat-sym c 'n 'hcn)))))
                                                                            (function/lam [['hl (strict-below c 'n)]] 'hl))]
                                                      (subst-nat c (g-at 'f 'n c 't) (nat-sym (g-at 'f 'n c 't) c (g-when 'f 'n c 't hd false-value c))
                                                                 (function/lam [['z nat]] (strict-below 'z 'n)) c-below)))))
                             Pa (fn [bound] (function/lam [['a nat]] (exists-nat (function/lam [['b nat]] (conj* (strict-below 'a 'b) (conj* (at-most 'b bound) (eq-nat (app g 'a) (app g 'b))))))))]
                         (app (app 'ih g g-bound) goal
                              (function/lam
                               [['a nat] ['ha (app (Pa 'n) 'a)]]
                               (app 'ha goal
                                    (function/lam
                                     [['b nat] ['pb (conj* (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app g 'a) (app g 'b))))]]
                                     (let [hab (pleft (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app g 'a) (app g 'b))) 'pb)
                                           inner (pright (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app g 'a) (app g 'b))) 'pb)
                                           hbn (pleft (at-most 'b 'n) (eq-nat (app g 'a) (app g 'b)) inner)
                                           hg (pright (at-most 'b 'n) (eq-nat (app g 'a) (app g 'b)) inner)
                                           han (amt 'a 'b 'n (amt 'a (succ 'a) 'b (at-most-succ 'a) hab) hbn)
                                           fa (app 'f 'a) fb (app 'f 'b)
                                           same (eq-nat fa fb)
                                           finish (fn [heq] (make-repeat 'f n1 'a 'b hab (amt 'b 'n n1 hbn (at-most-succ 'n)) heq))]
                                       (on-decision
                                        'f 'n 'a goal
                                        (fn [hda]
                                          (on-decision
                                           'f 'n 'b goal
                                           ;; both below n: g = f on both
                                           (fn [hdb] (finish (nat-trans fa (g-at 'f 'n c 'a) fb (nat-sym (g-at 'f 'n c 'a) fa (g-when 'f 'n c 'a hda true-value fa))
                                                                        (nat-trans (g-at 'f 'n c 'a) (g-at 'f 'n c 'b) fb hg (g-when 'f 'n c 'b hdb true-value fb)))))
                                           ;; a below, b squeezed: f a = g a = g b = c, impossible
                                           (fn [hdb] (explode goal (app 'hno 'a han
                                                                        (nat-trans fa (g-at 'f 'n c 'a) c (nat-sym (g-at 'f 'n c 'a) fa (g-when 'f 'n c 'a hda true-value fa))
                                                                                   (nat-trans (g-at 'f 'n c 'a) (g-at 'f 'n c 'b) c hg (g-when 'f 'n c 'b hdb false-value c))))))))
                                        (fn [hda]
                                          (on-decision
                                           'f 'n 'b goal
                                           ;; a squeezed, b below: f b = g b = g a = c, impossible
                                           (fn [hdb] (explode goal (app 'hno 'b hbn
                                                                        (nat-trans fb (g-at 'f 'n c 'b) c (nat-sym (g-at 'f 'n c 'b) fb (g-when 'f 'n c 'b hdb true-value fb))
                                                                                   (nat-trans (g-at 'f 'n c 'b) (g-at 'f 'n c 'a) c (nat-sym (g-at 'f 'n c 'a) (g-at 'f 'n c 'b) hg)
                                                                                              (g-when 'f 'n c 'a hda false-value c))))))
                                           ;; both squeezed: both are n
                                           (fn [hdb] (finish (nat-trans fa 'n fb (top 'a han hda) (nat-sym fb 'n (top 'b hbn hdb))))))))))))))))))
         'n))})

(def theorem-specs [trichotomy-spec bounded-search-spec pigeonhole-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      divmod/extend-environment
      decide-completeness/extend-environment
      (support/extend-with :nat-pigeonhole theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
