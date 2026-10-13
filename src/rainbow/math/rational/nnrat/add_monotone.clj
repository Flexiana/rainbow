(ns rainbow.math.rational.nnrat.add-monotone
  "Universal (one-sided) monotonicity of nonnegative-rational addition under the
  rational order -- the additive companion to nnrat/multiply-monotone, and the
  keystone for convex-combination / weighted-average bounds:

      add-right-monotone-base : base-at-most a b -> base-at-most (a+c) (b+c)  (all c a b)
      add-right-monotone      : a <= b           -> (a+c) <= (b+c)           (all c a b)

  Base lemma is pure nat.  With num/den written out and the packed product
  denominators expanded by the nnrat/denominator-combine law, the goal
      ((n_a*d_c) + (n_c*d_a)) * (d_b*d_c)  <=  ((n_b*d_c) + (n_c*d_b)) * (d_a*d_c)
  right-distributes (nat/multiply-add-left) into a sum of two products on each side,
  compared summand-wise by nat/add-monotone:
    * the a-summand reduces -- via two EXACT nat/multiply-four-reorder rewrites, no
      commutation -- to nat/multiply-right-monotone applied to the hypothesis
      (n_a*d_b <= n_b*d_a) scaled by (d_c*d_c);
    * the c-summand is an equality (four-reorder nc da db dc), lifted to <= from
      nat/at-most-reflexive.
  The denominators are transported between packed succ(combine ..) and product form
  with equality/congruent-function over the combine law.  The full theorem lifts the
  base lemma across the reflexive-transitive closure nnrat/at-most exactly as
  nnrat/multiply-monotone does: apply the closure recursor at motive (\\y. a+c <= y+c),
  reflexivity for the base and at-most-from-cross + at-most-transitive per step.

  Native and axiom-free; chains rainbow.algorithms.proofs.decision-guarantee-audit (order),
  nat-order / nat-semiring (nat algebra), and nonnegative-rational."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def successor (function/const* 'data/succ []))

(defn- nsucc [v] (function/app successor v))
(defn- nmul [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nadd [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- symmetric [l r same]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r same))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- transitive-nat [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- nat-add-commutative [l r]
  (function/app (function/const* 'nat/add-commutative []) l r))
(defn- nat-multiply-commutative [l r]
  (function/app (function/const* 'nat/multiply-commutative []) l r))
(defn- four-reorder [a b c d]
  (function/app (function/const* 'nat/multiply-four-reorder []) a b c d))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left [])
                left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right [])
                left right replacement same ordered))

(defn- rnum [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- radd [a c] (function/app (function/const* 'nnrat/add []) a c))
(defn- base-le [a b] (function/app (function/const* 'nnrat/base-at-most []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))

;; base one-sided add monotonicity: base-at-most a b -> base-at-most (a+c) (b+c)
(def add-right-monotone-base-spec
  {:name 'nnrat/add-right-monotone-base :universes []
   :type (function/forall
          [['c nnrat] ['a nnrat] ['b nnrat]
           ['h (base-le 'a 'b)]]
          (base-le (radd 'a 'c) (radd 'b 'c)))
   :value
   (function/lam
    [['c nnrat] ['a nnrat] ['b nnrat] ['h (base-le 'a 'b)]]
    (let [na (rnum 'a) nb (rnum 'b) nc (rnum 'c)
          dpa (dpre 'a) dpb (dpre 'b) dpc (dpre 'c)
          da (nsucc dpa) db (nsucc dpb) dc (nsucc dpc)
          ;; numerator / denominator of the two sums
          num-ac (nadd (nmul na dc) (nmul nc da))
          num-bc (nadd (nmul nb dc) (nmul nc db))
          den-ac (nsucc (combine dpa dpc))
          den-bc (nsucc (combine dpb dpc))
          comb-law-ac (function/app (function/const* 'nnrat/denominator-combine [])
                                    dpa dpc)             ; den-ac = da*dc
          comb-law-bc (function/app (function/const* 'nnrat/denominator-combine [])
                                    dpb dpc)             ; den-bc = db*dc
          ;; product-denominator and distributed forms
          L (nmul num-ac (nmul db dc))
          R (nmul num-bc (nmul da dc))
          t1-l (nmul (nmul na dc) (nmul db dc))
          t2-l (nmul (nmul nc da) (nmul db dc))
          t1-r (nmul (nmul nb dc) (nmul da dc))
          t2-r (nmul (nmul nc db) (nmul da dc))
          dist-l (function/app (function/const* 'nat/multiply-add-left [])
                               (nmul na dc) (nmul nc da) (nmul db dc)) ; L = t1-l + t2-l
          dist-r (function/app (function/const* 'nat/multiply-add-left [])
                               (nmul nb dc) (nmul nc db) (nmul da dc)) ; R = t1-r + t2-r
          ;; T1 : t1-l <= t1-r, from h (n_a*d_b <= n_b*d_a) scaled by (d_c*d_c)
          scaled-l (nmul (nmul na db) (nmul dc dc))
          scaled-r (nmul (nmul nb da) (nmul dc dc))
          rm-t1 (function/app (function/const* 'nat/multiply-right-monotone [])
                              (nmul dc dc) (nmul na db) (nmul nb da) 'h)
          t1a (rewrite-left t1-l scaled-l scaled-r (four-reorder na dc db dc) rm-t1)
          T1 (rewrite-right t1-l scaled-r t1-r
                            (symmetric t1-r scaled-r (four-reorder nb dc da dc))
                            t1a)
          ;; T2 : t2-l <= t2-r, an equality (four-reorder nc da db dc) lifted from reflexive
          T2 (rewrite-left t2-l t2-r t2-r
                           (four-reorder nc da db dc)
                           (function/app (function/const* 'nat/at-most-reflexive []) t2-r))
          ;; core : L' <= R'
          core (function/app (function/const* 'nat/add-monotone [])
                             t1-l t1-r t2-l t2-r T1 T2)
          s1 (rewrite-left L (nadd t1-l t2-l) (nadd t1-r t2-r) dist-l core)
          s2 (rewrite-right L (nadd t1-r t2-r) R
                            (symmetric R (nadd t1-r t2-r) dist-r) s1)
          g-left (nmul num-ac den-bc)
          g-right (nmul num-bc den-ac)
          cong-l (congruent (function/lam [['v nat]] (nmul num-ac 'v))
                            den-bc (nmul db dc) comb-law-bc)          ; g-left = L
          cong-r (congruent (function/lam [['v nat]] (nmul num-bc 'v))
                            den-ac (nmul da dc) comb-law-ac)          ; g-right = R
          s3 (rewrite-left g-left L R cong-l s2)
          s4 (rewrite-right g-left R g-right
                            (symmetric g-right R cong-r) s3)]
      s4))})

;; full one-sided monotonicity across the closure: a <= b -> (a+c) <= (b+c)
(def add-right-monotone-spec
  {:name 'nnrat/add-right-monotone :universes []
   :type (function/forall
          [['c nnrat] ['a nnrat] ['b nnrat]
           ['h (rat-le 'a 'b)]]
          (rat-le (radd 'a 'c) (radd 'b 'c)))
   :value
   (function/lam
    [['c nnrat] ['a nnrat] ['b nnrat] ['h (rat-le 'a 'b)]]
    (let [motive (function/lam [['y nnrat]]
                               (rat-le (radd 'a 'c) (radd 'y 'c)))
          step (function/lam
                [['before nnrat] ['after nnrat]
                 ['o (base-le 'before 'after)]
                 ['acc (rat-le (radd 'a 'c) (radd 'before 'c))]]
                (let [lifted (function/app
                              (function/const* 'nnrat/at-most-from-cross [])
                              (radd 'before 'c) (radd 'after 'c)
                              (function/app
                               (function/const* 'nnrat/add-right-monotone-base [])
                               'c 'before 'after 'o))]
                  (function/app (function/const* 'nnrat/at-most-transitive [])
                                (radd 'a 'c) (radd 'before 'c) (radd 'after 'c)
                                'acc lifted)))
          base-case (function/app (function/const* 'nnrat/at-most-reflexive [])
                                  (radd 'a 'c))]
      (function/app 'h motive step base-case)))})

;; addition commutes up to nnrat equivalence: (a+b) ~ (b+a)
;; equivalent unfolds to Eq nat (num(a+b)*den(b+a)) (num(b+a)*den(a+b)); prove by
;; commuting the numerator sum (nat/add-commutative) and the product denominator
;; (nat/multiply-commutative), transported through the denominator-combine law.
(def add-commutative-spec
  {:name 'nnrat/add-commutative :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
                          (equiv (radd 'a 'b) (radd 'b 'a)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [na (rnum 'a) nb (rnum 'b)
          dpa (dpre 'a) dpb (dpre 'b)
          da (nsucc dpa) db (nsucc dpb)
          n-ab (nadd (nmul na db) (nmul nb da))
          n-ba (nadd (nmul nb da) (nmul na db))
          d-ab (nsucc (combine dpa dpb))
          d-ba (nsucc (combine dpb dpa))
          law-ab (function/app (function/const* 'nnrat/denominator-combine []) dpa dpb)
          law-ba (function/app (function/const* 'nnrat/denominator-combine []) dpb dpa)
          ;; n-ab*d-ba = n-ab*(db*da)
          e1 (congruent (function/lam [['v nat]] (nmul n-ab 'v)) d-ba (nmul db da) law-ba)
          ;; n-ab*(db*da) = n-ab*(da*db)
          e2 (congruent (function/lam [['v nat]] (nmul n-ab 'v))
                        (nmul db da) (nmul da db) (nat-multiply-commutative db da))
          ;; n-ab*(da*db) = n-ba*(da*db)
          e3 (congruent (function/lam [['v nat]] (nmul 'v (nmul da db)))
                        n-ab n-ba (nat-add-commutative (nmul na db) (nmul nb da)))
          ;; n-ba*(da*db) = n-ba*d-ab
          e4 (congruent (function/lam [['v nat]] (nmul n-ba 'v))
                        (nmul da db) d-ab (symmetric d-ab (nmul da db) law-ab))]
      (transitive-nat (nmul n-ab d-ba) (nmul n-ab (nmul db da))
                      (nmul n-ba d-ab)
                      e1
                      (transitive-nat (nmul n-ab (nmul db da)) (nmul n-ab (nmul da db))
                                      (nmul n-ba d-ab)
                                      e2
                                      (transitive-nat (nmul n-ab (nmul da db))
                                                      (nmul n-ba (nmul da db))
                                                      (nmul n-ba d-ab)
                                                      e3 e4)))))})

;; left-sided monotonicity: a <= b -> (c+a) <= (c+b), via commutativity + respects-equiv
(def add-left-monotone-spec
  {:name 'nnrat/add-left-monotone :universes []
   :type (function/forall
          [['c nnrat] ['a nnrat] ['b nnrat]
           ['h (rat-le 'a 'b)]]
          (rat-le (radd 'c 'a) (radd 'c 'b)))
   :value
   (function/lam
    [['c nnrat] ['a nnrat] ['b nnrat] ['h (rat-le 'a 'b)]]
    (function/app
     (function/const* 'nnrat/at-most-respects-equivalence [])
     (radd 'c 'a) (radd 'a 'c) (radd 'c 'b) (radd 'b 'c)
     (function/app (function/const* 'nnrat/add-commutative []) 'c 'a)
     (function/app (function/const* 'nnrat/add-commutative []) 'c 'b)
     (function/app (function/const* 'nnrat/add-right-monotone []) 'c 'a 'b 'h)))})

;; two-sided monotonicity: a<=a' -> b<=b' -> (a+b) <= (a'+b')
(def add-monotone-spec
  {:name 'nnrat/add-monotone :universes []
   :type (function/forall
          [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
           ['ha (rat-le 'a 'a-hi)] ['hb (rat-le 'b 'b-hi)]]
          (rat-le (radd 'a 'b) (radd 'a-hi 'b-hi)))
   :value
   (function/lam
    [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
     ['ha (rat-le 'a 'a-hi)] ['hb (rat-le 'b 'b-hi)]]
    (function/app
     (function/const* 'nnrat/at-most-transitive [])
     (radd 'a 'b) (radd 'a-hi 'b) (radd 'a-hi 'b-hi)
     (function/app (function/const* 'nnrat/add-right-monotone []) 'b 'a 'a-hi 'ha)
     (function/app (function/const* 'nnrat/add-left-monotone []) 'a-hi 'b 'b-hi 'hb)))})

(def definition-specs [])
(def theorem-specs [add-right-monotone-base-spec add-right-monotone-spec
                    add-commutative-spec add-left-monotone-spec add-monotone-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-add-monotone
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
