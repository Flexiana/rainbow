(ns rainbow.data.binary
  "Binary (positional) numerals -- foundation stone for magnitude-INDEPENDENT
  arithmetic.

  Motivation: `data/Nat` is unary (a succ-chain), so kernel reduction of nat/nnrat
  arithmetic costs O(magnitude). That is the recurring 'LP ceiling is magnitude'
  wall and the reason the verified-scaling bridge is impractical past one
  dimension (see the design notes and memory
  rainbow-scaling-bridge-magnitude-wall). A positional numeral whose arithmetic
  recurses on O(log magnitude) constructors reduces in O(log) steps; a certified
  `Bin <-> Nat` bridge then lets the numeric layer pay log cost while keeping the
  Nat-based theorems.

  This module is the first brick: the `data/Bin` inductive and its recursor.
    data/Bin  ::=  bin-zero              -- 0
               |   bin-even half         -- 2 * half
               |   bin-odd  half         -- 2 * half + 1
  (Non-canonical: bin-even bin-zero also denotes 0; canonicalisation and the
  Bin<->Nat interpretation/arithmetic are the next bricks.)

  The block installs cleanly and its recursor `data/Bin.rec` reduces (verified in
  binary_test by a fold into Nat). Additive and opt-in: it adds a block to a
  checked environment via `extend-environment`, mirroring rainbow.data.list; it
  does not touch the trusted base."
  (:require [rainbow.module :as module]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as function]))

(def type-level [:succ [:zero]])

(def bin-spec
  {:block/schema-version 1
   :block/alias 'data/Bin
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'data/bin-zero :constructor/fields []}
    {:constructor/alias 'data/bin-even
     :constructor/fields [{:field/name 'half :field/type [:self]}]}
    {:constructor/alias 'data/bin-odd
     :constructor/fields [{:field/name 'half :field/type [:self]}]}]})

;; ---- bin/to-nat : the value interpretation (Bin -> Nat) ---------------------
;;
;;   to-nat bin-zero      = 0
;;   to-nat (bin-even h)  = 2 * to-nat h
;;   to-nat (bin-odd  h)  = 2 * to-nat h + 1
;;
;; via data/Bin.rec, with doubling by data/Nat.rec (2*n = n's succ-succ fold).
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private Bin (function/const* 'data/Bin []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- nat-rec [level motive zero-case succ-case target]
  (function/app (function/const* 'data/Nat.rec [level]) motive zero-case succ-case target))
(defn- bin-rec [level motive zero-case even-case odd-case target]
  (function/app (function/const* 'data/Bin.rec [level]) motive zero-case even-case odd-case target))

;; bin/double n = 2*n, by Nat.rec: 0 -> 0 ; succ p -> succ (succ (double p)).
;; Named + reducible so proofs unfold it cleanly (inline lambdas leave redexes the
;; defeq cannot resolve). double (succ k) reduces definitionally to succ (succ (double k)).
(def double-spec
  {:name 'bin/double
   :universes []
   :type (function/arrow nat nat)
   :value (function/lam [['n nat]]
                        (nat-rec type-level (function/lam [['x nat]] nat) zero
                                 (function/lam [['p nat] ['ih nat]] (succ (succ 'ih))) 'n))})
(defn- double* [n] (function/app (function/const* 'bin/double []) n))

(def to-nat-spec
  {:name 'bin/to-nat
   :universes []
   :type (function/arrow Bin nat)
   :value
   (function/lam
    [['b Bin]]
    (bin-rec type-level (function/lam [['x Bin]] nat)
             zero
             (function/lam [['h Bin] ['ih nat]] (double* 'ih))
             (function/lam [['h Bin] ['ih nat]] (succ (double* 'ih)))
             'b))})
(defn- to-nat* [b] (function/app (function/const* 'bin/to-nat []) b))

;; bin/bin-succ : Bin -> Bin -- increment with carry.
;;   bin-zero -> bin-odd bin-zero ; bin-even h -> bin-odd h ; bin-odd h -> bin-even (succ h)
(def bin-succ-spec
  {:name 'bin/bin-succ
   :universes []
   :type (function/arrow Bin Bin)
   :value
   (function/lam
    [['b Bin]]
    (bin-rec type-level (function/lam [['x Bin]] Bin)
             (function/app (function/const* 'data/bin-odd []) (function/const* 'data/bin-zero []))
             (function/lam [['h Bin] ['ih Bin]] (function/app (function/const* 'data/bin-odd []) 'h))
             (function/lam [['h Bin] ['ih Bin]] (function/app (function/const* 'data/bin-even []) 'ih))
             'b))})
(defn- bin-succ* [b] (function/app (function/const* 'bin/bin-succ []) b))

;; bin/from-nat : Nat -> Bin, by Nat.rec: 0 -> bin-zero ; succ p -> bin-succ (from-nat p)
(def from-nat-spec
  {:name 'bin/from-nat
   :universes []
   :type (function/arrow nat Bin)
   :value (function/lam [['n nat]]
                        (nat-rec type-level (function/lam [['x nat]] Bin)
                                 (function/const* 'data/bin-zero [])
                                 (function/lam [['p nat] ['ih Bin]] (bin-succ* 'ih)) 'n))})
(defn- from-nat* [n] (function/app (function/const* 'bin/from-nat []) n))

;; bin/bit-length : Bin -> Nat -- the number of digit constructors. A structural
;; O(log magnitude) operation: on 2^k (bin-even^k bin-zero, k constructors) it
;; reduces in O(k) steps, whereas to-nat of the same value is 2^k in unary and is
;; unreachable. This is the concrete demonstration that Bin operations are
;; magnitude-INDEPENDENT (the point of the whole module).
(def bit-length-spec
  {:name 'bin/bit-length
   :universes []
   :type (function/arrow Bin nat)
   :value
   (function/lam
    [['b Bin]]
    (function/app (function/const* 'data/Bin.rec [type-level])
                  (function/lam [['x Bin]] nat)
                  zero
                  (function/lam [['h Bin] ['ih nat]] (succ 'ih))
                  (function/lam [['h Bin] ['ih nat]] (succ 'ih))
                  'b))})

;; ---- bin/bin-add : O(log) binary addition (LSB-first, carry via bin-succ) ----
;;   add bin-zero b = b
;;   add (bin-even a') (bin-even b') = bin-even (add a' b')      ; add (bin-even a') (bin-odd b') = bin-odd (add a' b')
;;   add (bin-odd a')  (bin-even b') = bin-odd  (add a' b')      ; add (bin-odd a')  (bin-odd b')  = bin-even (bin-succ (add a' b'))
;; Recursion on a returns a Bin->Bin that recurses on b; the carry in the odd/odd
;; case is one bin-succ. Correct on concrete inputs (see binary_test); the general
;; correctness theorem to-nat (add a b) = nat-add (to-nat a) (to-nat b) is the next
;; brick (a double induction with double-distributes-over-add lemmas).
(def ^:private arrow-bin-bin (function/arrow Bin Bin))
(defn- be* [x] (function/app (function/const* 'data/bin-even []) x))
(defn- bo* [x] (function/app (function/const* 'data/bin-odd []) x))
(def bin-add-spec
  {:name 'bin/bin-add
   :universes []
   :type (function/arrow Bin arrow-bin-bin)
   :value
   (function/lam
    [['a Bin] ['b Bin]]
    (function/app
     (bin-rec type-level (function/lam [['x Bin]] arrow-bin-bin)
              (function/lam [['b Bin]] 'b)                                  ; add bin-zero = id
              (function/lam [['a2 Bin] ['ih arrow-bin-bin]]                 ; a = bin-even a2
                            (function/lam [['b Bin]]
                                          (bin-rec type-level (function/lam [['x Bin]] Bin)
                                                   (be* 'a2)
                                                   (function/lam [['b2 Bin] ['ihb Bin]] (be* (function/app 'ih 'b2)))
                                                   (function/lam [['b2 Bin] ['ihb Bin]] (bo* (function/app 'ih 'b2)))
                                                   'b)))
              (function/lam [['a2 Bin] ['ih arrow-bin-bin]]                 ; a = bin-odd a2
                            (function/lam [['b Bin]]
                                          (bin-rec type-level (function/lam [['x Bin]] Bin)
                                                   (bo* 'a2)
                                                   (function/lam [['b2 Bin] ['ihb Bin]] (bo* (function/app 'ih 'b2)))
                                                   (function/lam [['b2 Bin] ['ihb Bin]] (be* (bin-succ* (function/app 'ih 'b2))))
                                                   'b)))
              'a)
     'b))})

;; ---- faithfulness: to-nat (from-nat n) = n ---------------------------------
(def ^:private bin-zero-term (function/const* 'data/bin-zero []))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- refl-nat [x] (function/app (function/const* 'equality/reflexive [type-level]) nat x))
(defn- congr-nat [ff x y h]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat ff x y h))
(defn- trans-nat [x y w hxy hyw]
  (function/app (function/const* 'equality/transitive [type-level]) nat x y w hxy hyw))
(def ^:private succ-fn (function/lam [['k nat]] (succ 'k)))
(def ^:private double-const (function/const* 'bin/double []))
(defn- support-at [b] (function/app (function/const* 'bin/to-nat-of-bin-succ []) b))

;; support lemma: to-nat (bin-succ b) = succ (to-nat b), by Bin.rec (Prop motive
;; -> recursor level [:zero]). bin-zero/bin-even discharge by reflexivity (both
;; sides defeq); bin-odd needs the IH, lifted through double by congruence
;; (double (succ k) reduces to succ (succ (double k)) definitionally).
(def to-nat-of-bin-succ-spec
  {:name 'bin/to-nat-of-bin-succ
   :universes []
   :type (function/forall [['b Bin]]
                          (eq-nat (to-nat* (bin-succ* 'b)) (succ (to-nat* 'b))))
   :value
   (function/lam
    [['b Bin]]
    (bin-rec [:zero]
             (function/lam [['b Bin]] (eq-nat (to-nat* (bin-succ* 'b)) (succ (to-nat* 'b))))
             (refl-nat (to-nat* (bin-succ* bin-zero-term)))
             (function/lam [['h Bin] ['ih (eq-nat (to-nat* (bin-succ* 'h)) (succ (to-nat* 'h)))]]
                           (refl-nat (to-nat* (bin-succ* (be* 'h)))))
             (function/lam [['h Bin] ['ih (eq-nat (to-nat* (bin-succ* 'h)) (succ (to-nat* 'h)))]]
                           (congr-nat double-const (to-nat* (bin-succ* 'h)) (succ (to-nat* 'h)) 'ih))
             'b))})

;; the faithfulness theorem: to-nat (from-nat n) = n, by Nat.rec (Prop motive
;; -> level [:zero]); the succ case chains the support lemma with succ-congruence
;; on the IH.
(def to-nat-from-nat-spec
  {:name 'bin/to-nat-from-nat
   :universes []
   :type (function/forall [['n nat]] (eq-nat (to-nat* (from-nat* 'n)) 'n))
   :value
   (function/lam
    [['n nat]]
    (nat-rec [:zero]
             (function/lam [['n nat]] (eq-nat (to-nat* (from-nat* 'n)) 'n))
             (refl-nat (to-nat* (from-nat* zero)))
             (function/lam [['p nat] ['ih (eq-nat (to-nat* (from-nat* 'p)) 'p)]]
                           (trans-nat (to-nat* (bin-succ* (from-nat* 'p)))
                                      (succ (to-nat* (from-nat* 'p)))
                                      (succ 'p)
                                      (support-at (from-nat* 'p))
                                      (congr-nat succ-fn (to-nat* (from-nat* 'p)) 'p 'ih)))
             'n))})

;; ---- bin-add correctness: to-nat (bin-add a b) = nat-add (to-nat a) (to-nat b) ----
(defn- na [x y] (function/app (function/const* 'algebra/nat-add []) x y))
(defn- esym [x y h] (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- azr [x] (function/app (function/const* 'algebra/nat-add-zero-right []) x))
(defn- asr [x y] (function/app (function/const* 'algebra/nat-add-successor-right []) x y))
(def ^:private ss-fn (function/lam [['k nat]] (succ (succ 'k))))
(def ^:private nat-zero (function/const* 'data/zero []))

;; double distributes over nat-add:  double (na x y) = na (double x) (double y)
;; by Nat.rec on x (Prop motive over y -> level [:zero]).
(def double-distributes-add-spec
  {:name 'bin/double-distributes-add
   :universes []
   :type (function/forall [['x nat] ['y nat]] (eq-nat (double* (na 'x 'y)) (na (double* 'x) (double* 'y))))
   :value
   (function/lam
    [['x nat]]
    (nat-rec [:zero]
             (function/lam [['x nat]] (function/forall [['y nat]] (eq-nat (double* (na 'x 'y)) (na (double* 'x) (double* 'y)))))
             (function/lam [['y nat]] (refl-nat (double* 'y)))
             (function/lam [['p nat] ['ih (function/forall [['y nat]] (eq-nat (double* (na 'p 'y)) (na (double* 'p) (double* 'y))))]]
                           (function/lam [['y nat]]
                                         (congr-nat ss-fn (double* (na 'p 'y)) (na (double* 'p) (double* 'y)) (function/app 'ih 'y))))
             'x))})
(defn- ddist* [x y] (function/app (function/const* 'bin/double-distributes-add []) x y))
(defn- to-nat-of-bin-succ* [b] (function/app (function/const* 'bin/to-nat-of-bin-succ []) b))

;; the correctness theorem, by double Bin.rec (Prop motive -> level [:zero]).
(defn- add-motive [a] (function/forall [['b Bin]] (eq-nat (to-nat* (function/app (function/const* 'bin/bin-add []) a 'b))
                                                          (na (to-nat* a) (to-nat* 'b)))))
(defn- badd [a b] (function/app (function/const* 'bin/bin-add []) a b))
(def to-nat-bin-add-spec
  {:name 'bin/to-nat-bin-add
   :universes []
   :type (function/forall [['a Bin] ['b Bin]] (eq-nat (to-nat* (badd 'a 'b)) (na (to-nat* 'a) (to-nat* 'b))))
   :value
   (function/lam
    [['a Bin]]
    (bin-rec [:zero] (function/lam [['a Bin]] (add-motive 'a))
             (function/lam [['b Bin]] (refl-nat (to-nat* 'b)))
             ;; a = bin-even a2
             (function/lam [['a2 Bin] ['ih (add-motive 'a2)]]
                           (function/lam [['b Bin]]
                                         (bin-rec [:zero]
                                                  (function/lam [['b Bin]] (eq-nat (to-nat* (badd (be* 'a2) 'b)) (na (double* (to-nat* 'a2)) (to-nat* 'b))))
                                                  (esym (na (double* (to-nat* 'a2)) nat-zero) (double* (to-nat* 'a2)) (azr (double* (to-nat* 'a2))))
                                                  (function/lam [['b2 Bin] ['ihb (eq-nat (to-nat* (badd (be* 'a2) 'b2)) (na (double* (to-nat* 'a2)) (to-nat* 'b2)))]]
                                                                (trans-nat (double* (to-nat* (badd 'a2 'b2))) (double* (na (to-nat* 'a2) (to-nat* 'b2))) (na (double* (to-nat* 'a2)) (double* (to-nat* 'b2)))
                                                                           (congr-nat double-const (to-nat* (badd 'a2 'b2)) (na (to-nat* 'a2) (to-nat* 'b2)) (function/app 'ih 'b2))
                                                                           (ddist* (to-nat* 'a2) (to-nat* 'b2))))
                                                  (function/lam [['b2 Bin] ['ihb (eq-nat (to-nat* (badd (be* 'a2) 'b2)) (na (double* (to-nat* 'a2)) (to-nat* 'b2)))]]
                                                                (let [A (to-nat* 'a2) B (to-nat* 'b2)
                                                                      e12 (trans-nat (double* (to-nat* (badd 'a2 'b2))) (double* (na A B)) (na (double* A) (double* B))
                                                                                     (congr-nat double-const (to-nat* (badd 'a2 'b2)) (na A B) (function/app 'ih 'b2)) (ddist* A B))]
                                                                  (trans-nat (succ (double* (to-nat* (badd 'a2 'b2)))) (succ (na (double* A) (double* B))) (na (double* A) (succ (double* B)))
                                                                             (congr-nat succ-fn (double* (to-nat* (badd 'a2 'b2))) (na (double* A) (double* B)) e12)
                                                                             (esym (na (double* A) (succ (double* B))) (succ (na (double* A) (double* B))) (asr (double* A) (double* B))))))
                                                  'b)))
             ;; a = bin-odd a2
             (function/lam [['a2 Bin] ['ih (add-motive 'a2)]]
                           (function/lam [['b Bin]]
                                         (bin-rec [:zero]
                                                  (function/lam [['b Bin]] (eq-nat (to-nat* (badd (bo* 'a2) 'b)) (na (succ (double* (to-nat* 'a2))) (to-nat* 'b))))
                                                  (esym (na (succ (double* (to-nat* 'a2))) nat-zero) (succ (double* (to-nat* 'a2))) (azr (succ (double* (to-nat* 'a2)))))
                                                  (function/lam [['b2 Bin] ['ihb (eq-nat (to-nat* (badd (bo* 'a2) 'b2)) (na (succ (double* (to-nat* 'a2))) (to-nat* 'b2)))]]
                                                                (let [A (to-nat* 'a2) B (to-nat* 'b2)
                                                                      e12 (trans-nat (double* (to-nat* (badd 'a2 'b2))) (double* (na A B)) (na (double* A) (double* B))
                                                                                     (congr-nat double-const (to-nat* (badd 'a2 'b2)) (na A B) (function/app 'ih 'b2)) (ddist* A B))]
                                                                  (congr-nat succ-fn (double* (to-nat* (badd 'a2 'b2))) (na (double* A) (double* B)) e12)))
                                                  (function/lam [['b2 Bin] ['ihb (eq-nat (to-nat* (badd (bo* 'a2) 'b2)) (na (succ (double* (to-nat* 'a2))) (to-nat* 'b2)))]]
                                                                (let [A (to-nat* 'a2) B (to-nat* 'b2)
                                                                      e12 (trans-nat (double* (to-nat* (badd 'a2 'b2))) (double* (na A B)) (na (double* A) (double* B))
                                                                                     (congr-nat double-const (to-nat* (badd 'a2 'b2)) (na A B) (function/app 'ih 'b2)) (ddist* A B))
                                                                      iLHS (trans-nat (double* (to-nat* (bin-succ* (badd 'a2 'b2)))) (succ (succ (double* (to-nat* (badd 'a2 'b2))))) (succ (succ (na (double* A) (double* B))))
                                                                                      (congr-nat double-const (to-nat* (bin-succ* (badd 'a2 'b2))) (succ (to-nat* (badd 'a2 'b2))) (to-nat-of-bin-succ* (badd 'a2 'b2)))
                                                                                      (congr-nat ss-fn (double* (to-nat* (badd 'a2 'b2))) (na (double* A) (double* B)) e12))
                                                                      iRHS (congr-nat succ-fn (na (double* A) (succ (double* B))) (succ (na (double* A) (double* B))) (asr (double* A) (double* B)))]
                                                                  (trans-nat (double* (to-nat* (bin-succ* (badd 'a2 'b2)))) (succ (succ (na (double* A) (double* B)))) (na (succ (double* A)) (succ (double* B)))
                                                                             iLHS (esym (na (succ (double* A)) (succ (double* B))) (succ (succ (na (double* A) (double* B)))) iRHS))))
                                                  'b)))
             'a))})

;; ---- bin/bin-multiply : O(log) binary multiplication ------------------------
(defn- mul [x y] (function/app (function/const* 'nat/multiply []) x y))
(defn- mul-add-left [a b c] (function/app (function/const* 'nat/multiply-add-left []) a b c)) ; (a+b)*c = a*c+b*c
(def ^:private one (succ nat-zero))

;; double y = y + y  (Nat.rec on y; succ case uses add-successor-right)
(def double-self-spec
  {:name 'bin/double-self
   :universes []
   :type (function/forall [['y nat]] (eq-nat (double* 'y) (na 'y 'y)))
   :value
   (function/lam
    [['y nat]]
    (nat-rec [:zero] (function/lam [['y nat]] (eq-nat (double* 'y) (na 'y 'y)))
             (refl-nat (double* nat-zero))
             (function/lam [['p nat] ['ih (eq-nat (double* 'p) (na 'p 'p))]]
                           (trans-nat (succ (succ (double* 'p))) (succ (succ (na 'p 'p))) (succ (na 'p (succ 'p)))
                                      (congr-nat ss-fn (double* 'p) (na 'p 'p) 'ih)
                                      (esym (succ (na 'p (succ 'p))) (succ (succ (na 'p 'p)))
                                            (congr-nat succ-fn (na 'p (succ 'p)) (succ (na 'p 'p)) (asr 'p 'p)))))
             'y))})
(defn- double-self* [y] (function/app (function/const* 'bin/double-self []) y))

;; double (x*y) = (double x)*y  (via double-self + right-distributivity)
(def double-multiply-left-spec
  {:name 'bin/double-multiply-left
   :universes []
   :type (function/forall [['x nat] ['y nat]] (eq-nat (double* (mul 'x 'y)) (mul (double* 'x) 'y)))
   :value
   (function/lam
    [['x nat] ['y nat]]
    (trans-nat (double* (mul 'x 'y)) (na (mul 'x 'y) (mul 'x 'y)) (mul (double* 'x) 'y)
               (double-self* (mul 'x 'y))
               (esym (mul (double* 'x) 'y) (na (mul 'x 'y) (mul 'x 'y))
                     (trans-nat (mul (double* 'x) 'y) (mul (na 'x 'x) 'y) (na (mul 'x 'y) (mul 'x 'y))
                                (congr-nat (function/lam [['k nat]] (mul 'k 'y)) (double* 'x) (na 'x 'x) (double-self* 'x))
                                (mul-add-left 'x 'x 'y)))))})
(defn- double-mul-left* [x y] (function/app (function/const* 'bin/double-multiply-left []) x y))

(defn- badd [a b] (function/app (function/const* 'bin/bin-add []) a b))
;; bin/bin-multiply : recursion on a; even a' -> bin-even (a'*b); odd a' -> b + bin-even (a'*b)
(def bin-multiply-spec
  {:name 'bin/bin-multiply
   :universes []
   :type (function/arrow Bin arrow-bin-bin)
   :value
   (function/lam
    [['a Bin] ['b Bin]]
    (function/app
     (bin-rec type-level (function/lam [['x Bin]] arrow-bin-bin)
              (function/lam [['b Bin]] bin-zero-term)
              (function/lam [['a2 Bin] ['ih arrow-bin-bin]]
                            (function/lam [['b Bin]] (be* (function/app 'ih 'b))))
              (function/lam [['a2 Bin] ['ih arrow-bin-bin]]
                            (function/lam [['b Bin]] (badd 'b (be* (function/app 'ih 'b)))))
              'a)
     'b))})
(defn- bmul [a b] (function/app (function/const* 'bin/bin-multiply []) a b))
(defn- to-nat-bin-add* [x y] (function/app (function/const* 'bin/to-nat-bin-add []) x y))

;; correctness: to-nat (bin-multiply a b) = nat-multiply (to-nat a) (to-nat b)
;; by Bin.rec on a; odd case uses bin-add correctness + double-multiply-left + right-distributivity.
(defn- mul-motive [a] (function/forall [['b Bin]] (eq-nat (to-nat* (bmul a 'b)) (mul (to-nat* a) (to-nat* 'b)))))
(def to-nat-bin-multiply-spec
  {:name 'bin/to-nat-bin-multiply
   :universes []
   :type (function/forall [['a Bin] ['b Bin]] (eq-nat (to-nat* (bmul 'a 'b)) (mul (to-nat* 'a) (to-nat* 'b))))
   :value
   (function/lam
    [['a Bin]]
    (bin-rec [:zero] (function/lam [['a Bin]] (mul-motive 'a))
             (function/lam [['b Bin]] (refl-nat (to-nat* (bmul bin-zero-term 'b))))
             ;; a = bin-even a2
             (function/lam [['a2 Bin] ['ih (mul-motive 'a2)]]
                           (function/lam [['b Bin]]
                                         (trans-nat (double* (to-nat* (bmul 'a2 'b))) (double* (mul (to-nat* 'a2) (to-nat* 'b))) (mul (double* (to-nat* 'a2)) (to-nat* 'b))
                                                    (congr-nat double-const (to-nat* (bmul 'a2 'b)) (mul (to-nat* 'a2) (to-nat* 'b)) (function/app 'ih 'b))
                                                    (double-mul-left* (to-nat* 'a2) (to-nat* 'b)))))
             ;; a = bin-odd a2
             (function/lam [['a2 Bin] ['ih (mul-motive 'a2)]]
                           (function/lam [['b Bin]]
                                         (trans-nat (to-nat* (bmul (bo* 'a2) 'b)) (na (to-nat* 'b) (double* (mul (to-nat* 'a2) (to-nat* 'b)))) (mul (succ (double* (to-nat* 'a2))) (to-nat* 'b))
                                                    (trans-nat (to-nat* (bmul (bo* 'a2) 'b)) (na (to-nat* 'b) (double* (to-nat* (bmul 'a2 'b)))) (na (to-nat* 'b) (double* (mul (to-nat* 'a2) (to-nat* 'b))))
                                                               (to-nat-bin-add* 'b (be* (bmul 'a2 'b)))
                                                               (congr-nat (function/lam [['k nat]] (na (to-nat* 'b) (double* 'k))) (to-nat* (bmul 'a2 'b)) (mul (to-nat* 'a2) (to-nat* 'b)) (function/app 'ih 'b)))
                                                    (trans-nat (na (to-nat* 'b) (double* (mul (to-nat* 'a2) (to-nat* 'b)))) (na (to-nat* 'b) (mul (double* (to-nat* 'a2)) (to-nat* 'b))) (mul (succ (double* (to-nat* 'a2))) (to-nat* 'b))
                                                               (congr-nat (function/lam [['k nat]] (na (to-nat* 'b) 'k)) (double* (mul (to-nat* 'a2) (to-nat* 'b))) (mul (double* (to-nat* 'a2)) (to-nat* 'b)) (double-mul-left* (to-nat* 'a2) (to-nat* 'b)))
                                                               ;; M2 = na y (mul (double A) y) is DEFINITIONALLY (mul (succ (double A)) y) = T2,
                                                               ;; since nat/multiply recurses left: (succ p)*y -> y + p*y. So this step is refl.
                                                               ;; (mul-add-left would drag in mul one y = na y 0, which is STUCK -- na recurses left.)
                                                               (refl-nat (mul (succ (double* (to-nat* 'a2))) (to-nat* 'b)))))))
             'a))})

;; ---- bin/at-most : O(log) binary comparison (LSB-first) ---------------------
;; The strict-less case forces a MUTUAL recursion: comparing (bin-odd a')(bin-even b')
;; is 2a'+1 <= 2b' <=> a' < b', which needs strict-below, while (bin-odd a')(bin-odd b')
;; is a' <= b'. So we carry BOTH le and lt together as a Product Bool Bool via
;; bin/compare, recursing on a (giving Bin -> Product) then on b (applying the ih to
;; b's half), exactly the bin-add shape. bin/at-most = first o compare.
;;   compare 0 b            = (true, nonzero b)            -- 0 <= b always; 0 < b <=> b != 0
;;   compare (be a') 0      = (le a' 0, false)
;;   compare (be a') (be b')= (le a' b', lt a' b')  = compare a' b'
;;   compare (be a') (bo b')= (le a' b', le a' b')         -- 2a'<=2b'+1 and 2a'<2b'+1 both <=> a'<=b'
;;   compare (bo a') 0      = (false, false)
;;   compare (bo a') (be b')= (lt a' b', lt a' b')         -- 2a'+1<=2b' and <2b' both <=> a'<b'
;;   compare (bo a') (bo b')= (le a' b', lt a' b')  = compare a' b'
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private btrue (function/const* 'data/true []))
(def ^:private bfalse (function/const* 'data/false []))
(def ^:private prod-bb (function/app (function/const* 'data/Product [type-level type-level]) bool bool))
(defn- mk-pair [x y] (function/app (function/const* 'data/pair [type-level type-level]) bool bool x y))
(defn- pfst [s] (function/app (function/const* 'product/first [type-level type-level]) bool bool s))
(defn- psnd [s] (function/app (function/const* 'product/second [type-level type-level]) bool bool s))

;; bin/nonzero : Bin -> Bool -- b != 0 (true on any bin-odd, recurse through bin-even).
(def nonzero-spec
  {:name 'bin/nonzero
   :universes []
   :type (function/arrow Bin bool)
   :value (function/lam [['b Bin]]
                        (bin-rec type-level (function/lam [['x Bin]] bool)
                                 bfalse
                                 (function/lam [['h Bin] ['ih bool]] 'ih)
                                 (function/lam [['h Bin] ['ih bool]] btrue)
                                 'b))})
(defn- nonzero* [b] (function/app (function/const* 'bin/nonzero []) b))

(def ^:private arrow-bin-prod (function/arrow Bin prod-bb))
(def compare-spec
  {:name 'bin/compare
   :universes []
   :type (function/arrow Bin arrow-bin-prod)
   :value
   (function/lam
    [['a Bin] ['b Bin]]
    (function/app
     (bin-rec type-level (function/lam [['x Bin]] arrow-bin-prod)
              ;; a = 0
              (function/lam [['b Bin]] (mk-pair btrue (nonzero* 'b)))
              ;; a = bin-even a2 ; ih = compare a2 : Bin -> Product
              (function/lam [['a2 Bin] ['ih arrow-bin-prod]]
                            (function/lam [['b Bin]]
                                          (bin-rec type-level (function/lam [['x Bin]] prod-bb)
                                                   (mk-pair (pfst (function/app 'ih (function/const* 'data/bin-zero []))) bfalse)
                                                   (function/lam [['b2 Bin] ['ihb prod-bb]] (function/app 'ih 'b2))
                                                   (function/lam [['b2 Bin] ['ihb prod-bb]] (mk-pair (pfst (function/app 'ih 'b2)) (pfst (function/app 'ih 'b2))))
                                                   'b)))
              ;; a = bin-odd a2 ; ih = compare a2 : Bin -> Product
              (function/lam [['a2 Bin] ['ih arrow-bin-prod]]
                            (function/lam [['b Bin]]
                                          (bin-rec type-level (function/lam [['x Bin]] prod-bb)
                                                   (mk-pair bfalse bfalse)
                                                   (function/lam [['b2 Bin] ['ihb prod-bb]] (mk-pair (psnd (function/app 'ih 'b2)) (psnd (function/app 'ih 'b2))))
                                                   (function/lam [['b2 Bin] ['ihb prod-bb]] (mk-pair (pfst (function/app 'ih 'b2)) (psnd (function/app 'ih 'b2))))
                                                   'b)))
              'a)
     'b))})
(defn- compare* [a b] (function/app (function/const* 'bin/compare []) a b))

(def at-most-spec
  {:name 'bin/at-most
   :universes []
   :type (function/arrow Bin (function/arrow Bin bool))
   :value (function/lam [['a Bin] ['b Bin]] (pfst (compare* 'a 'b)))})

;; ---- general correctness: bin/at-most a b = nat/decide-at-most (to-nat a)(to-nat b) ----
;; The structural (O(log)) comparison is proved to agree with the unary Nat decider
;; through to-nat. The bridge needs "halving" facts relating the decider on doubled
;; arguments to the decider on the halves; each is a small induction whose steps are
;; the decider's definitional succ/succ cancellation plus the IH (no arithmetic
;; lemmas). The strengthened invariant bin/compare-reflects carries BOTH le and lt
;; (as a Product of the two equalities) so the mutual odd/even recursion goes through.
(def ^:private prop-level [:zero])
(defn- nat-rec-prop [motive zc sc t]
  (function/app (function/const* 'data/Nat.rec [prop-level]) motive zc sc t))
(defn- bin-rec-prop [motive zc ec oc t]
  (function/app (function/const* 'data/Bin.rec [prop-level]) motive zc ec oc t))
(defn- dam [a b] (function/app (function/const* 'nat/decide-at-most []) a b))
(defn- eq-bool [x y] (function/equality type-level bool x y))
(defn- refl-bool [x] (function/app (function/const* 'equality/reflexive [type-level]) bool x))
(defn- sym-bool [x y h] (function/app (function/const* 'equality/symmetric [type-level]) bool x y h))
(defn- trans-bool [x y w hxy hyw]
  (function/app (function/const* 'equality/transitive [type-level]) bool x y w hxy hyw))

;; H1 : decide-at-most (double A) (double B) = decide-at-most A B
(def decide-double-double-spec
  {:name 'bin/decide-double-double
   :universes []
   :type (function/forall [['A nat] ['B nat]] (eq-bool (dam (double* 'A) (double* 'B)) (dam 'A 'B)))
   :value
   (function/lam [['A nat]]
                 (nat-rec-prop
                  (function/lam [['A nat]] (function/forall [['B nat]] (eq-bool (dam (double* 'A) (double* 'B)) (dam 'A 'B))))
                  (function/lam [['B nat]] (refl-bool (dam zero 'B)))
                  (function/lam [['k nat] ['ihk (function/forall [['B nat]] (eq-bool (dam (double* 'k) (double* 'B)) (dam 'k 'B)))]]
                                (function/lam [['B nat]]
                                              (nat-rec-prop
                                               (function/lam [['B nat]] (eq-bool (dam (double* (succ 'k)) (double* 'B)) (dam (succ 'k) 'B)))
                                               (refl-bool (dam (succ 'k) zero))
                                               (function/lam [['j nat] ['ihb (eq-bool (dam (double* (succ 'k)) (double* 'j)) (dam (succ 'k) 'j))]]
                                                             (function/app 'ihk 'j))
                                               'B)))
                  'A))})
(defn- h1* [A B] (function/app (function/const* 'bin/decide-double-double []) A B))

;; H2 : decide-at-most (double A) (succ (double B)) = decide-at-most A B
(def decide-double-succ-double-spec
  {:name 'bin/decide-double-succ-double
   :universes []
   :type (function/forall [['A nat] ['B nat]] (eq-bool (dam (double* 'A) (succ (double* 'B))) (dam 'A 'B)))
   :value
   (function/lam [['A nat]]
                 (nat-rec-prop
                  (function/lam [['A nat]] (function/forall [['B nat]] (eq-bool (dam (double* 'A) (succ (double* 'B))) (dam 'A 'B))))
                  (function/lam [['B nat]] (refl-bool (dam zero 'B)))
                  (function/lam [['k nat] ['ihk (function/forall [['B nat]] (eq-bool (dam (double* 'k) (succ (double* 'B))) (dam 'k 'B)))]]
                                (function/lam [['B nat]]
                                              (nat-rec-prop
                                               (function/lam [['B nat]] (eq-bool (dam (double* (succ 'k)) (succ (double* 'B))) (dam (succ 'k) 'B)))
                                               (refl-bool (dam (succ 'k) zero))
                                               (function/lam [['j nat] ['ihb (eq-bool (dam (double* (succ 'k)) (succ (double* 'j))) (dam (succ 'k) 'j))]]
                                                             (function/app 'ihk 'j))
                                               'B)))
                  'A))})
(defn- h2* [A B] (function/app (function/const* 'bin/decide-double-succ-double []) A B))

;; HZ : decide-at-most 1 (double m) = decide-at-most 1 m  (per-case reflexivity)
(def decide-one-double-spec
  {:name 'bin/decide-one-double
   :universes []
   :type (function/forall [['m nat]] (eq-bool (dam (succ zero) (double* 'm)) (dam (succ zero) 'm)))
   :value
   (function/lam [['m nat]]
                 (nat-rec-prop
                  (function/lam [['m nat]] (eq-bool (dam (succ zero) (double* 'm)) (dam (succ zero) 'm)))
                  (refl-bool (dam (succ zero) zero))
                  (function/lam [['k nat] ['ih (eq-bool (dam (succ zero) (double* 'k)) (dam (succ zero) 'k))]]
                                (refl-bool (dam (succ zero) (succ 'k))))
                  'm))})
(defn- hz* [m] (function/app (function/const* 'bin/decide-one-double []) m))

;; H3 : decide-at-most (succ (double A)) (double B) = decide-at-most (succ A) B  (A=0 base uses HZ)
(def decide-succ-double-double-spec
  {:name 'bin/decide-succ-double-double
   :universes []
   :type (function/forall [['A nat] ['B nat]] (eq-bool (dam (succ (double* 'A)) (double* 'B)) (dam (succ 'A) 'B)))
   :value
   (function/lam [['A nat]]
                 (nat-rec-prop
                  (function/lam [['A nat]] (function/forall [['B nat]] (eq-bool (dam (succ (double* 'A)) (double* 'B)) (dam (succ 'A) 'B))))
                  (function/lam [['B nat]] (hz* 'B))
                  (function/lam [['k nat] ['ihk (function/forall [['B nat]] (eq-bool (dam (succ (double* 'k)) (double* 'B)) (dam (succ 'k) 'B)))]]
                                (function/lam [['B nat]]
                                              (nat-rec-prop
                                               (function/lam [['B nat]] (eq-bool (dam (succ (double* (succ 'k))) (double* 'B)) (dam (succ (succ 'k)) 'B)))
                                               (refl-bool (dam (succ (succ 'k)) zero))
                                               (function/lam [['j nat] ['ihb (eq-bool (dam (succ (double* (succ 'k))) (double* 'j)) (dam (succ (succ 'k)) 'j))]]
                                                             (function/app 'ihk 'j))
                                               'B)))
                  'A))})
(defn- h3* [A B] (function/app (function/const* 'bin/decide-succ-double-double []) A B))

;; HL0 : decide-at-most (double A) 0 = decide-at-most A 0  (per-case reflexivity)
(def decide-double-zero-spec
  {:name 'bin/decide-double-zero
   :universes []
   :type (function/forall [['A nat]] (eq-bool (dam (double* 'A) zero) (dam 'A zero)))
   :value
   (function/lam [['A nat]]
                 (nat-rec-prop
                  (function/lam [['A nat]] (eq-bool (dam (double* 'A) zero) (dam 'A zero)))
                  (refl-bool (dam zero zero))
                  (function/lam [['k nat] ['ih (eq-bool (dam (double* 'k) zero) (dam 'k zero))]]
                                (refl-bool (dam (succ 'k) zero)))
                  'A))})
(defn- hl0* [A] (function/app (function/const* 'bin/decide-double-zero []) A))

;; nz : nonzero b = decide-at-most 1 (to-nat b)
(def nonzero-reflects-spec
  {:name 'bin/nonzero-reflects
   :universes []
   :type (function/forall [['b Bin]] (eq-bool (nonzero* 'b) (dam (succ zero) (to-nat* 'b))))
   :value
   (function/lam [['b Bin]]
                 (bin-rec-prop
                  (function/lam [['b Bin]] (eq-bool (nonzero* 'b) (dam (succ zero) (to-nat* 'b))))
                  (refl-bool (nonzero* bin-zero-term))
                  (function/lam [['b2 Bin] ['ih (eq-bool (nonzero* 'b2) (dam (succ zero) (to-nat* 'b2)))]]
                                (trans-bool (nonzero* 'b2) (dam (succ zero) (to-nat* 'b2)) (dam (succ zero) (double* (to-nat* 'b2)))
                                            'ih
                                            (sym-bool (dam (succ zero) (double* (to-nat* 'b2))) (dam (succ zero) (to-nat* 'b2)) (hz* (to-nat* 'b2)))))
                  (function/lam [['b2 Bin] ['ih (eq-bool (nonzero* 'b2) (dam (succ zero) (to-nat* 'b2)))]] (refl-bool btrue))
                  'b))})
(defn- nz* [b] (function/app (function/const* 'bin/nonzero-reflects []) b))

;; The strengthened invariant: (le,lt) reflect the decider, carried as a Product.
(defn- leeq [a b] (eq-bool (pfst (compare* a b)) (dam (to-nat* a) (to-nat* b))))
(defn- lteq [a b] (eq-bool (psnd (compare* a b)) (dam (succ (to-nat* a)) (to-nat* b))))
(defn- prod-prop [a b] (function/app (function/const* 'data/Product [prop-level prop-level]) (leeq a b) (lteq a b)))
(defn- pairP [a b hle hlt] (function/app (function/const* 'data/pair [prop-level prop-level]) (leeq a b) (lteq a b) hle hlt))
(defn- pfstP [a b pr] (function/app (function/const* 'product/first [prop-level prop-level]) (leeq a b) (lteq a b) pr))
(defn- psndP [a b pr] (function/app (function/const* 'product/second [prop-level prop-level]) (leeq a b) (lteq a b) pr))
(def ^:private compare-motive (function/lam [['a Bin]] (function/forall [['b Bin]] (prod-prop 'a 'b))))

(def ^:private cmp-zero-case
  (function/lam [['b Bin]] (pairP bin-zero-term 'b (refl-bool btrue) (nz* 'b))))

(def ^:private cmp-even-case
  (function/lam [['a2 Bin] ['ih2 (function/forall [['b Bin]] (prod-prop 'a2 'b))]]
                (function/lam [['b Bin]]
                              (bin-rec-prop (function/lam [['b Bin]] (prod-prop (be* 'a2) 'b))
                                            (pairP (be* 'a2) bin-zero-term
                                                   (trans-bool (pfst (compare* 'a2 bin-zero-term)) (dam (to-nat* 'a2) zero) (dam (double* (to-nat* 'a2)) zero)
                                                               (pfstP 'a2 bin-zero-term (function/app 'ih2 bin-zero-term))
                                                               (sym-bool (dam (double* (to-nat* 'a2)) zero) (dam (to-nat* 'a2) zero) (hl0* (to-nat* 'a2))))
                                                   (refl-bool bfalse))
                                            (function/lam [['b2 Bin] ['ihb (prod-prop (be* 'a2) 'b2)]]
                                                          (pairP (be* 'a2) (be* 'b2)
                                                                 (trans-bool (pfst (compare* 'a2 'b2)) (dam (to-nat* 'a2) (to-nat* 'b2)) (dam (double* (to-nat* 'a2)) (double* (to-nat* 'b2)))
                                                                             (pfstP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (double* (to-nat* 'a2)) (double* (to-nat* 'b2))) (dam (to-nat* 'a2) (to-nat* 'b2)) (h1* (to-nat* 'a2) (to-nat* 'b2))))
                                                                 (trans-bool (psnd (compare* 'a2 'b2)) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (dam (succ (double* (to-nat* 'a2))) (double* (to-nat* 'b2)))
                                                                             (psndP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (double* (to-nat* 'a2))) (double* (to-nat* 'b2))) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (h3* (to-nat* 'a2) (to-nat* 'b2))))))
                                            (function/lam [['b2 Bin] ['ihb (prod-prop (be* 'a2) 'b2)]]
                                                          (pairP (be* 'a2) (bo* 'b2)
                                                                 (trans-bool (pfst (compare* 'a2 'b2)) (dam (to-nat* 'a2) (to-nat* 'b2)) (dam (double* (to-nat* 'a2)) (succ (double* (to-nat* 'b2))))
                                                                             (pfstP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (double* (to-nat* 'a2)) (succ (double* (to-nat* 'b2)))) (dam (to-nat* 'a2) (to-nat* 'b2)) (h2* (to-nat* 'a2) (to-nat* 'b2))))
                                                                 (trans-bool (pfst (compare* 'a2 'b2)) (dam (to-nat* 'a2) (to-nat* 'b2)) (dam (succ (double* (to-nat* 'a2))) (succ (double* (to-nat* 'b2))))
                                                                             (pfstP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (double* (to-nat* 'a2))) (succ (double* (to-nat* 'b2)))) (dam (to-nat* 'a2) (to-nat* 'b2)) (h1* (to-nat* 'a2) (to-nat* 'b2))))))
                                            'b))))

(def ^:private cmp-odd-case
  (function/lam [['a2 Bin] ['ih2 (function/forall [['b Bin]] (prod-prop 'a2 'b))]]
                (function/lam [['b Bin]]
                              (bin-rec-prop (function/lam [['b Bin]] (prod-prop (bo* 'a2) 'b))
                                            (pairP (bo* 'a2) bin-zero-term (refl-bool bfalse) (refl-bool bfalse))
                                            (function/lam [['b2 Bin] ['ihb (prod-prop (bo* 'a2) 'b2)]]
                                                          (pairP (bo* 'a2) (be* 'b2)
                                                                 (trans-bool (psnd (compare* 'a2 'b2)) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (dam (succ (double* (to-nat* 'a2))) (double* (to-nat* 'b2)))
                                                                             (psndP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (double* (to-nat* 'a2))) (double* (to-nat* 'b2))) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (h3* (to-nat* 'a2) (to-nat* 'b2))))
                                                                 (trans-bool (psnd (compare* 'a2 'b2)) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (dam (succ (succ (double* (to-nat* 'a2)))) (double* (to-nat* 'b2)))
                                                                             (psndP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (succ (double* (to-nat* 'a2)))) (double* (to-nat* 'b2))) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (h1* (succ (to-nat* 'a2)) (to-nat* 'b2))))))
                                            (function/lam [['b2 Bin] ['ihb (prod-prop (bo* 'a2) 'b2)]]
                                                          (pairP (bo* 'a2) (bo* 'b2)
                                                                 (trans-bool (pfst (compare* 'a2 'b2)) (dam (to-nat* 'a2) (to-nat* 'b2)) (dam (succ (double* (to-nat* 'a2))) (succ (double* (to-nat* 'b2))))
                                                                             (pfstP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (double* (to-nat* 'a2))) (succ (double* (to-nat* 'b2)))) (dam (to-nat* 'a2) (to-nat* 'b2)) (h1* (to-nat* 'a2) (to-nat* 'b2))))
                                                                 (trans-bool (psnd (compare* 'a2 'b2)) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (dam (succ (succ (double* (to-nat* 'a2)))) (succ (double* (to-nat* 'b2))))
                                                                             (psndP 'a2 'b2 (function/app 'ih2 'b2))
                                                                             (sym-bool (dam (succ (succ (double* (to-nat* 'a2)))) (succ (double* (to-nat* 'b2)))) (dam (succ (to-nat* 'a2)) (to-nat* 'b2)) (h3* (to-nat* 'a2) (to-nat* 'b2))))))
                                            'b))))

(def compare-reflects-spec
  {:name 'bin/compare-reflects
   :universes []
   :type (function/forall [['a Bin] ['b Bin]] (prod-prop 'a 'b))
   :value (function/lam [['a Bin]]
                        (bin-rec-prop compare-motive cmp-zero-case cmp-even-case cmp-odd-case 'a))})

;; at-most correctness: bin/at-most a b reduces to (first (compare a b)), the le component.
(def at-most-reflects-spec
  {:name 'bin/at-most-reflects
   :universes []
   :type (function/forall [['a Bin] ['b Bin]] (eq-bool (function/app (function/const* 'bin/at-most []) 'a 'b) (dam (to-nat* 'a) (to-nat* 'b))))
   :value (function/lam [['a Bin] ['b Bin]]
                        (pfstP 'a 'b (function/app (function/const* 'bin/compare-reflects []) 'a 'b)))})

(def definition-specs
  [double-spec to-nat-spec bin-succ-spec from-nat-spec bin-add-spec bit-length-spec
   to-nat-of-bin-succ-spec to-nat-from-nat-spec
   double-distributes-add-spec to-nat-bin-add-spec
   double-self-spec double-multiply-left-spec
   bin-multiply-spec to-nat-bin-multiply-spec
   nonzero-spec compare-spec at-most-spec
   decide-double-double-spec decide-double-succ-double-spec decide-one-double-spec
   decide-succ-double-double-spec decide-double-zero-spec nonzero-reflects-spec
   compare-reflects-spec at-most-reflects-spec])

(defn- add-bin-block [checked-environment]
  (let [result (kernel/add-inductive-block checked-environment bin-spec)]
    (when-not (= :accepted (:status result))
      (throw (ex-info "data/Bin block rejected"
                      {:error/category :data-binary/block-rejected :result result})))
    (:environment result)))

(defn- elaborate! [environment surface]
  (let [result (elaborate/core-expression environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Binary definition failed elaboration"
                      {:error/category :data-binary/elaboration-failed :result result})))
    (:term result)))

(defn- add-definition [environment {:keys [name universes type value]}]
  (let [core-type (elaborate! environment type)
        core-value (elaborate! environment value)
        result
        (kernel/add-declaration
         environment
         {:rainbow/kind :definition
          :rainbow/aliases #{name}
          :rainbow/universes universes
          :rainbow/type core-type
          :rainbow/value core-value
          :rainbow/transparency :reducible
          :rainbow/dependencies (into (term/constants core-type)
                                      (term/constants core-value))
          :rainbow/provenance {:origin :native :producer :binary-numeral}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Binary definition rejected"
                      {:error/category :data-binary/definition-rejected
                       :name name :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-definition (add-bin-block checked-environment) definition-specs))

(defn extend-environment
  "Install the data/Bin inductive block (and its generated data/Bin.rec) plus the
  bin/to-nat interpretation into a checked environment. Additive; chain it once,
  like other block modules." [checked-environment]
  (module/install-module checked-environment 'rainbow.data.binary))
(defn block-aliases
  "The declarations this module introduces (the type, its constructors, and the
  generated recursor)."
  []
  '#{data/Bin data/bin-zero data/bin-even data/bin-odd data/Bin.rec
     bin/double bin/to-nat bin/bin-succ bin/from-nat bin/bin-add bin/bit-length
     bin/to-nat-of-bin-succ bin/to-nat-from-nat
     bin/double-distributes-add bin/to-nat-bin-add
     bin/double-self bin/double-multiply-left bin/bin-multiply bin/to-nat-bin-multiply
     bin/nonzero bin/compare bin/at-most
     bin/decide-double-double bin/decide-double-succ-double bin/decide-one-double
     bin/decide-succ-double-double bin/decide-double-zero bin/nonzero-reflects
     bin/compare-reflects bin/at-most-reflects})
