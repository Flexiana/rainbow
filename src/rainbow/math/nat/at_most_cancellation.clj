(ns rainbow.math.nat.at-most-cancellation
  "Real-analysis bedrock (roadmap step 1): cancellation for the nat order.

  ADDITIVE (step-1a): nat/at-most a b unfolds to (exists extra, a + extra = b), so
  cancellation is a witness manipulation -- extract the witness, reorder with the
  nat-ring tactic, cancel the common summand via nat/add-left-cancel:
    nat/at-most-add-right-cancel : (a + k) <= (b + k) -> a <= b
    nat/at-most-add-left-cancel  : (k + a) <= (k + b) -> a <= b

  MULTIPLICATIVE (step-1, the base-at-most-transitivity brick): cancel a POSITIVE right
  factor from an order comparison:
    nat/at-most-multiply-right-cancel : a*(succ f) <= b*(succ f) -> a <= b
  proved by case-splitting decide(a<=b) with the Bool.rec equality-motive -- true branch
  is decide-at-most-true-sound; false branch takes b<=a (decide-at-most-false-reverse),
  lifts to b*k <= a*k (multiply-right-monotone), derives a*k = b*k with the hypothesis
  (at-most-antisymmetric), cancels the positive factor to a = b
  (multiply-successor-right-cancel), and rewrites to a <= b.

  Native and axiom-free; chains rainbow.math.nat.ring on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))

(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- add-left-cancel [prefix l r same]
  (function/app (function/const* 'nat/add-left-cancel []) prefix l r same))
(defn- existence [pred] (function/app (function/const* 'proposition/existence [type-level]) nat pred))
(defn- use-witness [pred goal exists handler]
  (function/app (function/const* 'proposition/use-witness [type-level]) nat pred goal exists handler))
(defn- witness [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))
;; nat-ring proof term for an add/mul reordering equality
(defn- reorder [l r] (:proof (ring/prove-nat-eq l r)))

;; --- extra helpers for multiplicative cancellation ---
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- decide-at-most [a b] (function/app (function/const* 'nat/decide-at-most []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- reflexive-bool [v]
  (function/app (function/const* 'equality/reflexive [type-level]) bool v))
(defn- at-most-reflexive [v] (function/app (function/const* 'nat/at-most-reflexive []) v))
(defn- at-most-rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- at-most-rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- decide-true-sound [a b h]
  (function/app (function/const* 'nat/decide-at-most-true-sound []) a b h))
(defn- decide-false-reverse [a b h]
  (function/app (function/const* 'nat/decide-at-most-false-reverse []) a b h))
(defn- bool-rec [motive false-case true-case decision]
  (function/app (function/const* 'data/Bool.rec [[:zero]]) motive false-case true-case decision))
(def zero-nat (function/const* 'data/zero []))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- multiply-add-left [l r factor]
  (function/app (function/const* 'nat/multiply-add-left []) l r factor))
(defn- multiply-succ-right [value factor]
  (function/app (function/const* 'nat/multiply-successor-right []) value factor))
(defn- add-zero-right [value]
  (function/app (function/const* 'algebra/nat-add-zero-right []) value))
(defn- explode [goal falsity]
  (function/app (function/const* 'proposition/explode []) goal falsity))
(defn- zero-not-successor [value]
  (function/app (function/const* 'nat/zero-not-successor []) value))
(defn- nat-rec [motive base step n]
  (function/app (function/const* 'data/Nat.rec [[:zero]]) motive base step n))
(defn- at-most-add-left-cancel [a b k h]
  (function/app (function/const* 'nat/at-most-add-left-cancel []) a b k h))
(defn- sum-zero-left-app [x y h]
  (function/app (function/const* 'nat/sum-zero-left []) x y h))

;; ---- nat/at-most-add-right-cancel : (a+k) <= (b+k) -> a <= b -----------------
(def add-right-cancel-spec
  {:name 'nat/at-most-add-right-cancel :universes []
   :type (function/forall
          [['a nat] ['b nat] ['k nat]
           ['h (at-most (nadd 'a 'k) (nadd 'b 'k))]]
          (at-most 'a 'b))
   :value
   (function/lam
    [['a nat] ['b nat] ['k nat]
     ['h (at-most (nadd 'a 'k) (nadd 'b 'k))]]
    (use-witness
     (function/lam [['e nat]] (eq-nat (nadd (nadd 'a 'k) 'e) (nadd 'b 'k)))
     (at-most 'a 'b)
     'h
     (function/lam
      [['e nat] ['he (eq-nat (nadd (nadd 'a 'k) 'e) (nadd 'b 'k))]]
      (let [;; (a+e)+k = (a+k)+e  [ring] ; then = b+k  [he]
            step (transitive (nadd (nadd 'a 'e) 'k) (nadd (nadd 'a 'k) 'e) (nadd 'b 'k)
                             (reorder (nadd (nadd 'a 'e) 'k) (nadd (nadd 'a 'k) 'e)) 'he)
            ;; move k to the front on both sides to use add-left-cancel:
            ;; k+(a+e) = (a+e)+k = b+k = k+b
            kae-kb (transitive (nadd 'k (nadd 'a 'e)) (nadd (nadd 'a 'e) 'k) (nadd 'k 'b)
                               (reorder (nadd 'k (nadd 'a 'e)) (nadd (nadd 'a 'e) 'k))
                               (transitive (nadd (nadd 'a 'e) 'k) (nadd 'b 'k) (nadd 'k 'b)
                                           step
                                           (reorder (nadd 'b 'k) (nadd 'k 'b))))
            ae-b (add-left-cancel 'k (nadd 'a 'e) 'b kae-kb)]  ; a+e = b
        (witness (function/lam [['d nat]] (eq-nat (nadd 'a 'd) 'b)) 'e ae-b)))))})

;; ---- nat/at-most-add-left-cancel : (k+a) <= (k+b) -> a <= b ------------------
(def add-left-cancel-order-spec
  {:name 'nat/at-most-add-left-cancel :universes []
   :type (function/forall
          [['a nat] ['b nat] ['k nat]
           ['h (at-most (nadd 'k 'a) (nadd 'k 'b))]]
          (at-most 'a 'b))
   :value
   (function/lam
    [['a nat] ['b nat] ['k nat]
     ['h (at-most (nadd 'k 'a) (nadd 'k 'b))]]
    (use-witness
     (function/lam [['e nat]] (eq-nat (nadd (nadd 'k 'a) 'e) (nadd 'k 'b)))
     (at-most 'a 'b)
     'h
     (function/lam
      [['e nat] ['he (eq-nat (nadd (nadd 'k 'a) 'e) (nadd 'k 'b))]]
      (let [;; k+(a+e) = (k+a)+e = k+b  ->  a+e = b via add-left-cancel
            kae-kb (transitive (nadd 'k (nadd 'a 'e)) (nadd (nadd 'k 'a) 'e) (nadd 'k 'b)
                               (reorder (nadd 'k (nadd 'a 'e)) (nadd (nadd 'k 'a) 'e)) 'he)
            ae-b (add-left-cancel 'k (nadd 'a 'e) 'b kae-kb)]
        (witness (function/lam [['d nat]] (eq-nat (nadd 'a 'd) 'b)) 'e ae-b)))))})

;; ---- nat/sum-zero-left : (x + y = 0) -> (x = 0)  (via Nat.rec + zero-not-successor) --
(def sum-zero-left-spec
  {:name 'nat/sum-zero-left :universes []
   :type (function/forall [['x nat] ['y nat]
                           ['h (eq-nat (nadd 'x 'y) zero-nat)]]
                          (eq-nat 'x zero-nat))
   :value
   (function/lam
    [['x nat] ['y nat]]
    (nat-rec
     (function/lam [['xv nat]]
                   (function/arrow (eq-nat (nadd 'xv 'y) zero-nat) (eq-nat 'xv zero-nat)))
     ;; base x=0 : (0+y=0) -> (0=0)
     (function/lam [['h0 (eq-nat (nadd zero-nat 'y) zero-nat)]] (reflexive-nat zero-nat))
     ;; step x=succ prev : (succ prev + y = 0) -> (succ prev = 0), impossible
     (function/lam [['prev nat]
                    ['ih (function/arrow (eq-nat (nadd 'prev 'y) zero-nat) (eq-nat 'prev zero-nat))]]
                   (function/lam [['hs (eq-nat (nadd (succ 'prev) 'y) zero-nat)]]
                                 (explode (eq-nat (succ 'prev) zero-nat)
                                          (function/app (zero-not-successor (nadd 'prev 'y))
                                                        (symmetric (nadd (succ 'prev) 'y) zero-nat 'hs)))))
     'x))})

;; ---- nat/at-most-multiply-right-cancel : a*(succ f) <= b*(succ f) -> a <= b ---
(def multiply-right-cancel-spec
  {:name 'nat/at-most-multiply-right-cancel :universes []
   :type (function/forall
          [['a nat] ['b nat] ['f nat]
           ['h (at-most (nmul 'a (succ 'f)) (nmul 'b (succ 'f)))]]
          (at-most 'a 'b))
   :value
   (function/lam
    [['a nat] ['b nat] ['f nat]
     ['h (at-most (nmul 'a (succ 'f)) (nmul 'b (succ 'f)))]]
    (let [k (succ 'f)
          decision (decide-at-most 'a 'b)
          goal (at-most 'a 'b)
          motive (function/lam [['choice bool]]
                               (function/arrow (eq-bool decision 'choice) goal))
          true-case (function/lam
                     [['ht (eq-bool decision true-value)]]
                     (decide-true-sound 'a 'b 'ht))
          false-case
          (function/lam
           [['hf (eq-bool decision false-value)]]
           ;; b <= a : exists d, b + d = a
           (use-witness
            (function/lam [['d nat]] (eq-nat (nadd 'b 'd) 'a))
            goal
            (decide-false-reverse 'a 'b 'hf)
            (function/lam
             [['d nat] ['hd (eq-nat (nadd 'b 'd) 'a)]]
             (let [bk (nmul 'b k) dk (nmul 'd k)
                   a=bd (symmetric (nadd 'b 'd) 'a 'hd)                       ; a = b+d
                   cong-ak (congruent (function/lam [['v nat]] (nmul 'v k))
                                      'a (nadd 'b 'd) a=bd)                    ; a*k = (b+d)*k
                   dist (multiply-add-left 'b 'd k)                           ; (b+d)*k = b*k + d*k
                   ak=bkdk (transitive (nmul 'a k) (nmul (nadd 'b 'd) k) (nadd bk dk)
                                       cong-ak dist)                          ; a*k = b*k+d*k
                   ;; H : a*k <= b*k  ==>  (b*k+d*k) <= b*k
                   HH (at-most-rewrite-left (nadd bk dk) (nmul 'a k) bk
                                            (symmetric (nmul 'a k) (nadd bk dk) ak=bkdk) 'h)
                   ;; rewrite RHS b*k -> b*k + 0
                   HH2 (at-most-rewrite-right (nadd bk dk) bk (nadd bk zero-nat)
                                              (symmetric (nadd bk zero-nat) bk (add-zero-right bk)) HH)
                   ;; cancel prefix b*k : d*k <= 0
                   dk<=0 (at-most-add-left-cancel dk zero-nat bk HH2)
                   ;; d*k <= 0  ==>  d*k = 0
                   dk=0 (use-witness
                         (function/lam [['g nat]] (eq-nat (nadd dk 'g) zero-nat))
                         (eq-nat dk zero-nat)
                         dk<=0
                         (function/lam [['g nat] ['hg (eq-nat (nadd dk 'g) zero-nat)]]
                                       (sum-zero-left-app dk 'g 'hg)))
                   ;; d*(succ f) = d + d*f  ==>  d + d*f = 0  ==>  d = 0
                   dsf (multiply-succ-right 'd 'f)                            ; d*k = d + d*f
                   ddf=0 (transitive (nadd 'd (nmul 'd 'f)) dk zero-nat
                                     (symmetric dk (nadd 'd (nmul 'd 'f)) dsf) dk=0)
                   d=0 (sum-zero-left-app 'd (nmul 'd 'f) ddf=0)             ; d = 0
                   ;; a = b+d = b+0 = b
                   bd=b0 (congruent (function/lam [['v nat]] (nadd 'b 'v)) 'd zero-nat d=0)
                   a=b0 (transitive 'a (nadd 'b 'd) (nadd 'b zero-nat) a=bd bd=b0)
                   a=b (transitive 'a (nadd 'b zero-nat) 'b a=b0 (add-zero-right 'b))]
               (at-most-rewrite-right 'a 'a 'b a=b (at-most-reflexive 'a))))))]
      (function/app (bool-rec motive false-case true-case decision)
                    (reflexive-bool decision))))})

(def definition-specs [])
(def theorem-specs [add-right-cancel-spec add-left-cancel-order-spec
                    sum-zero-left-spec multiply-right-cancel-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nat-at-most-cancellation
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
