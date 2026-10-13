(ns rainbow.math.rational.binary.rational-order
  "Brick 5b of the binary-numeral roadmap: a Bin-NATIVE rational comparison, proved
  to agree with the trusted checker's rational decision `audit/decide-nnrat-at-most`.

  The checker decides `l <= r` for nonnegative rationals by the cross-multiplication
    audit/decide-nnrat-at-most l r = nat/decide-at-most (num l * den r) (num r * den l)
  on unary `Nat` -- which is where the magnitude ceiling bites (see memory
  rainbow-scaling-bridge-magnitude-wall). Here the SAME decision is expressed on
  `data/Bin` numerals:
    bin/decide-rat-at-most nl dl nr dr = bin/at-most (nl * dr) (nr * dl)   (all Bin)
  and proved equal, through `to-nat`, to the nat-level cross-multiply decision
  (`bin/decide-rat-at-most-reflects`), hence to `audit/decide-nnrat-at-most` whenever
  the Bin fields represent the rational's num/den (`bin/decide-rat-matches-audit`).

  This is ADDITIVE: it installs definitions into a Bin-extended checked environment
  and does NOT touch the trusted checker. It is the foundation a Bin-native checker
  (brick 5c) would wire in. Reuses `bin/at-most-reflects` and `bin/to-nat-bin-multiply`
  from rainbow.data.binary."
  (:require [rainbow.module :as module]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.term :as term]
            [rainbow.data.binary :as binary]
            [rainbow.math.logic.function :as function]))

(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private Bin (function/const* 'data/Bin []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- dam [a b] (function/app (function/const* 'nat/decide-at-most []) a b))
(defn- mul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- tn [b] (function/app (function/const* 'bin/to-nat []) b))
(defn- bmul [a b] (function/app (function/const* 'bin/bin-multiply []) a b))
(defn- bat-most [a b] (function/app (function/const* 'bin/at-most []) a b))
(defn- numr [x] (function/app (function/const* 'nnrat/numerator []) x))
(defn- denr [x] (function/app (function/const* 'nnrat/denominator []) x))
(defn- adn [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- badd [a b] (function/app (function/const* 'bin/bin-add []) a b))
(defn- tba [a b] (function/app (function/const* 'bin/to-nat-bin-add []) a b))
(defn- radd [p q] (function/app (function/const* 'nnrat/add []) p q))

(defn- eq-bool [x y] (function/equality type-level bool x y))
(defn- eq-nat [x y] (function/equality type-level nat x y))
(defn- refl-bool [x] (function/app (function/const* 'equality/reflexive [type-level]) bool x))
(defn- trans-bool [x y w hxy hyw]
  (function/app (function/const* 'equality/transitive [type-level]) bool x y w hxy hyw))
;; congruence into a nat -> bool function (rewrite a Nat argument under a Bool-valued f)
(defn- congr-nb [ff x y h]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat bool ff x y h))
;; congruence into a nat -> nat function (rewrite a Nat argument under a Nat-valued f)
(defn- congr-nn [ff x y h]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat ff x y h))
;; to-nat-bin-multiply nl dr : eq (to-nat (nl * dr)) (mul (to-nat nl) (to-nat dr))
(defn- tbm [a b] (function/app (function/const* 'bin/to-nat-bin-multiply []) a b))

;; ---- bin/decide-rat-at-most : the Bin-native cross-multiply-compare ----
(def decide-rat-at-most-spec
  {:name 'bin/decide-rat-at-most
   :universes []
   :type (function/arrow Bin Bin Bin Bin bool)
   :value (function/lam [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]]
                        (bat-most (bmul 'nl 'dr) (bmul 'nr 'dl)))})

;; ---- reflects: agrees with the nat-level cross-multiply decision, through to-nat ----
;; bin/decide-rat-at-most nl dl nr dr
;;   = bin/at-most (nl*dr) (nr*dl)                                  [def]
;;   = decide-at-most (to-nat(nl*dr)) (to-nat(nr*dl))              [at-most-reflects]
;;   = decide-at-most (tn nl * tn dr) (tn nr * tn dl)              [to-nat-bin-multiply, x2]
(def decide-rat-at-most-reflects-spec
  {:name 'bin/decide-rat-at-most-reflects
   :universes []
   :type (function/forall [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]]
                          (eq-bool (function/app (function/const* 'bin/decide-rat-at-most []) 'nl 'dl 'nr 'dr)
                                   (dam (mul (tn 'nl) (tn 'dr)) (mul (tn 'nr) (tn 'dl)))))
   :value
   (function/lam [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]]
                 (let [P1 (bmul 'nl 'dr) P2 (bmul 'nr 'dl)
                       mL (mul (tn 'nl) (tn 'dr)) mR (mul (tn 'nr) (tn 'dl))
                       reflects (function/app (function/const* 'bin/at-most-reflects []) P1 P2)  ; bat-most P1 P2 = dam (tn P1)(tn P2)
           ;; rewrite tn P1 -> mL under (\x. dam x (tn P2))
                       step1 (congr-nb (function/lam [['x nat]] (dam 'x (tn P2))) (tn P1) mL (tbm 'nl 'dr))
           ;; rewrite tn P2 -> mR under (\y. dam mL y)
                       step2 (congr-nb (function/lam [['y nat]] (dam mL 'y)) (tn P2) mR (tbm 'nr 'dl))]
                   (trans-bool (bat-most P1 P2) (dam (tn P1) (tn P2)) (dam mL mR)
                               reflects
                               (trans-bool (dam (tn P1) (tn P2)) (dam mL (tn P2)) (dam mL mR)
                                           step1 step2))))})

;; ---- bridge: agrees with audit/decide-nnrat-at-most when the Bin fields
;;      represent the rational's numerator/denominator ----
;; audit/decide-nnrat-at-most l r = decide-at-most (num l * den r) (num r * den l).
;; Given (tn nl = num l), (tn dl = den l), (tn nr = num r), (tn dr = den r), rewrite
;; the reflects RHS field by field.
(def decide-rat-matches-audit-spec
  {:name 'bin/decide-rat-matches-audit
   :universes []
   :type (function/forall
          [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
           ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
           ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]]
          (eq-bool (function/app (function/const* 'bin/decide-rat-at-most []) 'nl 'dl 'nr 'dr)
                   (function/app (function/const* 'audit/decide-nnrat-at-most []) 'l 'r)))
   :value
   (function/lam
    [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
     ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
     ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]]
    (let [;; reflects RHS = dam (tn nl * tn dr) (tn nr * tn dl)
          reflects (function/app (function/const* 'bin/decide-rat-at-most-reflects []) 'nl 'dl 'nr 'dr)
          ;; rewrite left cross-product tn nl -> num l, tn dr -> den r
          L0 (mul (tn 'nl) (tn 'dr))
          L1 (mul (numr 'l) (tn 'dr))
          L2 (mul (numr 'l) (denr 'r))
          R0 (mul (tn 'nr) (tn 'dl))
          R1 (mul (numr 'r) (tn 'dl))
          R2 (mul (numr 'r) (denr 'l))
          ;; step L: L0 -> L1 -> L2, lifted under (\x. dam x R0)
          cL1 (congr-nn (function/lam [['x nat]] (mul 'x (tn 'dr))) (tn 'nl) (numr 'l) 'hnl)   ; L0 = L1
          cL2 (congr-nn (function/lam [['y nat]] (mul (numr 'l) 'y)) (tn 'dr) (denr 'r) 'hdr)  ; L1 = L2
          liftL1 (congr-nb (function/lam [['x nat]] (dam 'x R0)) L0 L1 cL1)                     ; dam L0 R0 = dam L1 R0
          liftL2 (congr-nb (function/lam [['x nat]] (dam 'x R0)) L1 L2 cL2)                     ; dam L1 R0 = dam L2 R0
          ;; step R: R0 -> R1 -> R2, lifted under (\y. dam L2 y)
          cR1 (congr-nn (function/lam [['x nat]] (mul 'x (tn 'dl))) (tn 'nr) (numr 'r) 'hnr)   ; R0 = R1
          cR2 (congr-nn (function/lam [['y nat]] (mul (numr 'r) 'y)) (tn 'dl) (denr 'l) 'hdl)  ; R1 = R2
          liftR1 (congr-nb (function/lam [['y nat]] (dam L2 'y)) R0 R1 cR1)                     ; dam L2 R0 = dam L2 R1
          liftR2 (congr-nb (function/lam [['y nat]] (dam L2 'y)) R1 R2 cR2)                     ; dam L2 R1 = dam L2 R2
          decL (function/app (function/const* 'bin/decide-rat-at-most []) 'nl 'dl 'nr 'dr)]
      ;; chain: decL = dam L0 R0 = dam L1 R0 = dam L2 R0 = dam L2 R1 = dam L2 R2 = audit l r
      (trans-bool decL (dam L0 R0) (dam L2 R2)
                  reflects
                  (trans-bool (dam L0 R0) (dam L1 R0) (dam L2 R2)
                              liftL1
                              (trans-bool (dam L1 R0) (dam L2 R0) (dam L2 R2)
                                          liftL2
                                          (trans-bool (dam L2 R0) (dam L2 R1) (dam L2 R2)
                                                      liftR1 liftR2))))))})

;; ---- direct soundness: the Bin decision carries the checker's actual guarantee ----
;; (not merely "agrees with the audit decision" -- it entails the Prop order the
;; checker relies on). Composes reflects with the existing nat decider soundness.
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(defn- sym-bool [x y h] (function/app (function/const* 'equality/symmetric [type-level]) bool x y h))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- nat-true-sound [a b h] (function/app (function/const* 'nat/decide-at-most-true-sound []) a b h))
(defn- nat-false-reverse [a b h] (function/app (function/const* 'nat/decide-at-most-false-reverse []) a b h))
(defn- decide-rat [nl dl nr dr] (function/app (function/const* 'bin/decide-rat-at-most []) nl dl nr dr))
(defn- reflects [nl dl nr dr] (function/app (function/const* 'bin/decide-rat-at-most-reflects []) nl dl nr dr))

;; decide = true  ->  nat/at-most (num_l*den_r) (num_r*den_l)   (the base-at-most body)
(def decide-rat-at-most-true-sound-spec
  {:name 'bin/decide-rat-at-most-true-sound
   :universes []
   :type (function/forall
          [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
           ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) true-value)]]
          (nat-at-most (mul (tn 'nl) (tn 'dr)) (mul (tn 'nr) (tn 'dl))))
   :value
   (function/lam
    [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
     ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) true-value)]]
    (let [mL (mul (tn 'nl) (tn 'dr)) mR (mul (tn 'nr) (tn 'dl))
          dec (decide-rat 'nl 'dl 'nr 'dr)
          ;; Eq (dam mL mR) true  =  trans (sym reflects) h
          eq-dam-true (trans-bool (dam mL mR) dec true-value
                                  (sym-bool dec (dam mL mR) (reflects 'nl 'dl 'nr 'dr))
                                  'h)]
      (nat-true-sound mL mR eq-dam-true)))})

;; decide = false  ->  nat/at-most (num_r*den_l) (num_l*den_r)   (the reverse order)
(def decide-rat-at-most-false-reverse-spec
  {:name 'bin/decide-rat-at-most-false-reverse
   :universes []
   :type (function/forall
          [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
           ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) false-value)]]
          (nat-at-most (mul (tn 'nr) (tn 'dl)) (mul (tn 'nl) (tn 'dr))))
   :value
   (function/lam
    [['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
     ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) false-value)]]
    (let [mL (mul (tn 'nl) (tn 'dr)) mR (mul (tn 'nr) (tn 'dl))
          dec (decide-rat 'nl 'dl 'nr 'dr)
          eq-dam-false (trans-bool (dam mL mR) dec false-value
                                   (sym-bool dec (dam mL mR) (reflects 'nl 'dl 'nr 'dr))
                                   'h)]
      (nat-false-reverse mL mR eq-dam-false)))})

;; ---- nnrat-level soundness: the directly-5c-usable form ----
;; decide = true  ->  nnrat/at-most l r  (the checker's actual order), whenever the
;; four Bin fields represent l,r's num/den. This is what a Bin-native checker (5c)
;; would invoke: one lemma from the Bin decision to the trusted rational order.
(defn- sym-nat [x y h] (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- trans-nat [x y w hxy hyw] (function/app (function/const* 'equality/transitive [type-level]) nat x y w hxy hyw))
(defn- am-rewrite-left [x y z heq ham] (function/app (function/const* 'nat/at-most-rewrite-left []) x y z heq ham))
(defn- am-rewrite-right [x y z heq ham] (function/app (function/const* 'nat/at-most-rewrite-right []) x y z heq ham))
(defn- am-from-cross [l r h] (function/app (function/const* 'nnrat/at-most-from-cross []) l r h))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))

(def decide-rat-sound-spec
  {:name 'bin/decide-rat-sound
   :universes []
   :type (function/forall
          [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
           ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
           ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]
           ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) true-value)]]
          (nnrat-at-most 'l 'r))
   :value
   (function/lam
    [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
     ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
     ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]
     ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) true-value)]]
    (let [mL (mul (tn 'nl) (tn 'dr)) mR (mul (tn 'nr) (tn 'dl))
          cL (mul (numr 'l) (denr 'r)) cR (mul (numr 'r) (denr 'l))
          ts (function/app (function/const* 'bin/decide-rat-at-most-true-sound []) 'nl 'dl 'nr 'dr 'h)  ; nat/at-most mL mR
          ;; Eq cL mL  (rewrite-left needs Eq x y with x=cL, y=mL)
          eq-cL-mL (trans-nat cL (mul (tn 'nl) (denr 'r)) mL
                              (congr-nn (function/lam [['t nat]] (mul 't (denr 'r))) (numr 'l) (tn 'nl) (sym-nat (tn 'nl) (numr 'l) 'hnl))
                              (congr-nn (function/lam [['t nat]] (mul (tn 'nl) 't)) (denr 'r) (tn 'dr) (sym-nat (tn 'dr) (denr 'r) 'hdr)))
          ;; at-most cL mR
          step-left (am-rewrite-left cL mL mR eq-cL-mL ts)
          ;; Eq mR cR  (rewrite-right needs Eq y z with y=mR, z=cR)
          eq-mR-cR (trans-nat mR (mul (numr 'r) (tn 'dl)) cR
                              (congr-nn (function/lam [['t nat]] (mul 't (tn 'dl))) (tn 'nr) (numr 'r) 'hnr)
                              (congr-nn (function/lam [['t nat]] (mul (numr 'r) 't)) (tn 'dl) (denr 'l) 'hdl))
          ;; at-most cL cR  =  base-at-most l r  (definitional)
          step-right (am-rewrite-right cL mR cR eq-mR-cR step-left)]
      (am-from-cross 'l 'r step-right)))})

;; decide = false  ->  nnrat/at-most r l  (the reverse trusted order), same hypotheses.
(def decide-rat-false-reverse-spec
  {:name 'bin/decide-rat-false-reverse
   :universes []
   :type (function/forall
          [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
           ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
           ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]
           ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) false-value)]]
          (nnrat-at-most 'r 'l))
   :value
   (function/lam
    [['l nnrat] ['r nnrat] ['nl Bin] ['dl Bin] ['nr Bin] ['dr Bin]
     ['hnl (eq-nat (tn 'nl) (numr 'l))] ['hdl (eq-nat (tn 'dl) (denr 'l))]
     ['hnr (eq-nat (tn 'nr) (numr 'r))] ['hdr (eq-nat (tn 'dr) (denr 'r))]
     ['h (eq-bool (decide-rat 'nl 'dl 'nr 'dr) false-value)]]
    (let [mL (mul (tn 'nl) (tn 'dr)) mR (mul (tn 'nr) (tn 'dl))
          ;; base-at-most r l = nat/at-most (num r * den l) (num l * den r)
          cRl (mul (numr 'r) (denr 'l)) cLr (mul (numr 'l) (denr 'r))
          fr (function/app (function/const* 'bin/decide-rat-at-most-false-reverse []) 'nl 'dl 'nr 'dr 'h) ; nat/at-most mR mL
          ;; Eq cRl mR  (rewrite-left: x=cRl, y=mR). cRl=mul(num r)(den l), mR=mul(tn nr)(tn dl);
          ;; go cRl -> mul(num r)(tn dl) [rewrite den l -> tn dl] -> mR [rewrite num r -> tn nr].
          eq-cRl-mR (trans-nat cRl (mul (numr 'r) (tn 'dl)) mR
                               (congr-nn (function/lam [['t nat]] (mul (numr 'r) 't)) (denr 'l) (tn 'dl) (sym-nat (tn 'dl) (denr 'l) 'hdl))
                               (congr-nn (function/lam [['t nat]] (mul 't (tn 'dl))) (numr 'r) (tn 'nr) (sym-nat (tn 'nr) (numr 'r) 'hnr)))
          step-left (am-rewrite-left cRl mR mL eq-cRl-mR fr)                    ; nat/at-most cRl mL
          ;; Eq mL cLr  (rewrite-right: y=mL, z=cLr)
          eq-mL-cLr (trans-nat mL (mul (numr 'l) (tn 'dr)) cLr
                               (congr-nn (function/lam [['t nat]] (mul 't (tn 'dr))) (tn 'nl) (numr 'l) 'hnl)
                               (congr-nn (function/lam [['t nat]] (mul (numr 'l) 't)) (tn 'dr) (denr 'r) 'hdr))
          step-right (am-rewrite-right cRl mL cLr eq-mL-cLr step-left)]         ; nat/at-most cRl cLr = base-at-most r l
      (am-from-cross 'r 'l step-right)))})

;; ---- construction: build nnrat/add's num/den on Bin from the parts ----
;; nnrat/add p q = (num p * den q + num q * den p) / (den p * den q). Both the
;; numerator and the denominator reduce DEFINITIONALLY to those cross forms (the
;; make-PREDECESSOR-denominator convention cancels: succ(pred(den p * den q)) = den p
;; * den q since the product of two succ-headed nats is succ-headed). So the Bin
;; construction bin-add(np*dq)(nq*dp) / (dp*dq) represents num/den (nnrat/add p q),
;; proved through to-nat via to-nat-bin-add + to-nat-bin-multiply. No nnrat/add-internals
;; lemma needed. This is the last foundation piece feeding the signed layer's cross-sums.
(def to-nat-rat-add-num-spec
  {:name 'bin/to-nat-rat-add-num
   :universes []
   :type (function/forall
          [['p nnrat] ['q nnrat] ['np Bin] ['dp Bin] ['nq Bin] ['dq Bin]
           ['hnp (eq-nat (tn 'np) (numr 'p))] ['hdp (eq-nat (tn 'dp) (denr 'p))]
           ['hnq (eq-nat (tn 'nq) (numr 'q))] ['hdq (eq-nat (tn 'dq) (denr 'q))]]
          (eq-nat (tn (badd (bmul 'np 'dq) (bmul 'nq 'dp))) (numr (radd 'p 'q))))
   :value
   (function/lam
    [['p nnrat] ['q nnrat] ['np Bin] ['dp Bin] ['nq Bin] ['dq Bin]
     ['hnp (eq-nat (tn 'np) (numr 'p))] ['hdp (eq-nat (tn 'dp) (denr 'p))]
     ['hnq (eq-nat (tn 'nq) (numr 'q))] ['hdq (eq-nat (tn 'dq) (denr 'q))]]
    (let [s (badd (bmul 'np 'dq) (bmul 'nq 'dp))
          t1 (adn (tn (bmul 'np 'dq)) (tn (bmul 'nq 'dp)))
          t2 (adn (mul (tn 'np) (tn 'dq)) (tn (bmul 'nq 'dp)))
          t3 (adn (mul (tn 'np) (tn 'dq)) (mul (tn 'nq) (tn 'dp)))
          t4 (adn (mul (numr 'p) (denr 'q)) (mul (tn 'nq) (tn 'dp)))
          t5 (adn (mul (numr 'p) (denr 'q)) (mul (numr 'q) (denr 'p)))
          eqL (trans-nat (mul (tn 'np) (tn 'dq)) (mul (numr 'p) (tn 'dq)) (mul (numr 'p) (denr 'q))
                         (congr-nn (function/lam [['t nat]] (mul 't (tn 'dq))) (tn 'np) (numr 'p) 'hnp)
                         (congr-nn (function/lam [['t nat]] (mul (numr 'p) 't)) (tn 'dq) (denr 'q) 'hdq))
          eqR (trans-nat (mul (tn 'nq) (tn 'dp)) (mul (numr 'q) (tn 'dp)) (mul (numr 'q) (denr 'p))
                         (congr-nn (function/lam [['t nat]] (mul 't (tn 'dp))) (tn 'nq) (numr 'q) 'hnq)
                         (congr-nn (function/lam [['t nat]] (mul (numr 'q) 't)) (tn 'dp) (denr 'p) 'hdp))
          A  (tba (bmul 'np 'dq) (bmul 'nq 'dp))
          s1 (congr-nn (function/lam [['x nat]] (adn 'x (tn (bmul 'nq 'dp)))) (tn (bmul 'np 'dq)) (mul (tn 'np) (tn 'dq)) (tbm 'np 'dq))
          s2 (congr-nn (function/lam [['y nat]] (adn (mul (tn 'np) (tn 'dq)) 'y)) (tn (bmul 'nq 'dp)) (mul (tn 'nq) (tn 'dp)) (tbm 'nq 'dp))
          s3 (congr-nn (function/lam [['x nat]] (adn 'x (mul (tn 'nq) (tn 'dp)))) (mul (tn 'np) (tn 'dq)) (mul (numr 'p) (denr 'q)) eqL)
          s4 (congr-nn (function/lam [['y nat]] (adn (mul (numr 'p) (denr 'q)) 'y)) (mul (tn 'nq) (tn 'dp)) (mul (numr 'q) (denr 'p)) eqR)]
      (trans-nat (tn s) t1 t5 A
                 (trans-nat t1 t2 t5 s1
                            (trans-nat t2 t3 t5 s2
                                       (trans-nat t3 t4 t5 s3 s4))))))})

(def to-nat-rat-add-den-spec
  {:name 'bin/to-nat-rat-add-den
   :universes []
   :type (function/forall
          [['p nnrat] ['q nnrat] ['dp Bin] ['dq Bin]
           ['hdp (eq-nat (tn 'dp) (denr 'p))] ['hdq (eq-nat (tn 'dq) (denr 'q))]]
          (eq-nat (tn (bmul 'dp 'dq)) (denr (radd 'p 'q))))
   :value
   (function/lam
    [['p nnrat] ['q nnrat] ['dp Bin] ['dq Bin]
     ['hdp (eq-nat (tn 'dp) (denr 'p))] ['hdq (eq-nat (tn 'dq) (denr 'q))]]
    (let [A (tbm 'dp 'dq)
          eqD (trans-nat (mul (tn 'dp) (tn 'dq)) (mul (denr 'p) (tn 'dq)) (mul (denr 'p) (denr 'q))
                         (congr-nn (function/lam [['t nat]] (mul 't (tn 'dq))) (tn 'dp) (denr 'p) 'hdp)
                         (congr-nn (function/lam [['t nat]] (mul (denr 'p) 't)) (tn 'dq) (denr 'q) 'hdq))]
      (trans-nat (tn (bmul 'dp 'dq)) (mul (tn 'dp) (tn 'dq)) (mul (denr 'p) (denr 'q)) A eqD)))})

(def definition-specs
  [decide-rat-at-most-spec decide-rat-at-most-reflects-spec decide-rat-matches-audit-spec
   decide-rat-at-most-true-sound-spec decide-rat-at-most-false-reverse-spec
   decide-rat-sound-spec decide-rat-false-reverse-spec
   to-nat-rat-add-num-spec to-nat-rat-add-den-spec])

(defn- add-definition [environment {:keys [name universes type value]}]
  (let [core-type (elaborate/core-expression environment type)
        core-value (elaborate/core-expression environment value)]
    (when-not (= :elaborated (:status core-type))
      (throw (ex-info "bin-rational type failed elaboration"
                      {:error/category :bin-rational/elaboration-failed :name name :result core-type})))
    (when-not (= :elaborated (:status core-value))
      (throw (ex-info "bin-rational value failed elaboration"
                      {:error/category :bin-rational/elaboration-failed :name name :result core-value})))
    (let [ct (:term core-type) cv (:term core-value)
          result (kernel/add-declaration
                  environment
                  {:rainbow/kind :definition
                   :rainbow/aliases #{name}
                   :rainbow/universes universes
                   :rainbow/type ct
                   :rainbow/value cv
                   :rainbow/transparency :reducible
                   :rainbow/dependencies (into (term/constants ct) (term/constants cv))
                   :rainbow/provenance {:origin :native :producer :bin-rational-order}
                   :rainbow/schema-version 1})]
      (when-not (= :accepted (:status result))
        (throw (ex-info "bin-rational definition rejected"
                        {:error/category :bin-rational/definition-rejected :name name :result result})))
      (:environment result))))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-definition checked-environment definition-specs))

(defn extend-environment
  "Install the Bin-native rational comparison into a Bin-extended checked environment.
  Chain after rainbow.data.binary/extend-environment. Additive; trusted checker untouched." [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.binary.rational-order))
(defn block-aliases
  "The declarations this module introduces."
  []
  '#{bin/decide-rat-at-most bin/decide-rat-at-most-reflects bin/decide-rat-matches-audit
     bin/decide-rat-at-most-true-sound bin/decide-rat-at-most-false-reverse
     bin/decide-rat-sound bin/decide-rat-false-reverse
     bin/to-nat-rat-add-num bin/to-nat-rat-add-den})
