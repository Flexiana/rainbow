(ns rainbow.math.rational.signed.multiply-nonzero
  "General signed no-zero-divisors:
     signed/multiply-zero-split : (a*b ~ 0) -> (a ~ 0) or (b ~ 0)
     signed/multiply-nonzero    : not(a ~ 0) -> not(b ~ 0) -> not(a*b ~ 0).
  The signed pair unfolds a*b ~ 0 to (Pa*Pb + Na*Nb) ~ (Pa*Nb + Na*Pb), which is exactly the
  hypothesis of nnrat/multiply-difference-zero, giving Pa~Na or Pb~Nb, i.e. a~0 or b~0. This is the
  general no-zero-divisors that strict convexity needs for the weight product (generalizes
  signed/square-nonzero to distinct factors)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.multiply-difference-zero :as mdz]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- spos [d] (app (function/const* 'signed/positive []) d))
(defn- sneg [d] (app (function/const* 'signed/negative []) d))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nnadd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nnequiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nn-trans [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- nn-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- azr [q] (app (function/const* 'nnrat/add-zero-right []) q))
(defn- azl [q] (app (function/const* 'nnrat/add-zero-left []) q))
(defn- mult-diff-zero [p1 n1 p2 n2 h]
  (app (function/const* 'nnrat/multiply-difference-zero []) p1 n1 p2 n2 h))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(def ^:private falsity (function/const* 'proposition/falsity []))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))

;; From Px ~ Nx rebuild x ~ 0 (defeq nnequiv (Px+0) (0+Nx)).
(defn- x-zero [x h]
  (let [Px (spos x) Nx (sneg x)]
    (nn-trans (nnadd Px nnzero) Px (nnadd nnzero Nx)
              (azr Px)
              (nn-trans Px Nx (nnadd nnzero Nx) h (nn-sym (nnadd nnzero Nx) Nx (azl Nx))))))

(def multiply-zero-split-spec
  {:name 'signed/multiply-zero-split
   :universes []
   :type (function/forall [['a signed] ['b signed] ['hab (seqv (smul 'a 'b) szero)]]
                          (disjt (seqv 'a szero) (seqv 'b szero)))
   :value
   (function/lam
    [['a signed] ['b signed] ['hab (seqv (smul 'a 'b) szero)]]
    (let [ab (smul 'a 'b) Pab (spos ab) Nab (sneg ab)
          Pa (spos 'a) Na (sneg 'a) Pb (spos 'b) Nb (sneg 'b)
          ;; hab :defeq nnequiv (Pab+0) (0+Nab); strip the add-zeros -> Pab ~ Nab
          pabNab (nn-trans Pab (nnadd Pab nnzero) Nab
                           (nn-sym (nnadd Pab nnzero) Pab (azr Pab))
                           (nn-trans (nnadd Pab nnzero) (nnadd nnzero Nab) Nab 'hab (azl Nab)))
          ;; Pab :defeq Pa*Pb+Na*Nb, Nab :defeq Pa*Nb+Na*Pb
          split (mult-diff-zero Pa Na Pb Nb pabNab)                 ; (Pa~Na) or (Pb~Nb) [nnrat]
          goal (disjt (seqv 'a szero) (seqv 'b szero))]
      (use-disj (nnequiv Pa Na) (nnequiv Pb Nb) goal split
                (function/lam [['ha (nnequiv Pa Na)]]
                              (left-disj (seqv 'a szero) (seqv 'b szero) (x-zero 'a 'ha)))
                (function/lam [['hb (nnequiv Pb Nb)]]
                              (right-disj (seqv 'a szero) (seqv 'b szero) (x-zero 'b 'hb))))))})

(defn- mult-zero-split [a b h] (app (function/const* 'signed/multiply-zero-split []) a b h))

(def multiply-nonzero-spec
  {:name 'signed/multiply-nonzero
   :universes []
   :type (function/forall [['a signed] ['b signed]
                           ['ha (pneg (seqv 'a szero))] ['hb (pneg (seqv 'b szero))]]
                          (pneg (seqv (smul 'a 'b) szero)))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ha (pneg (seqv 'a szero))] ['hb (pneg (seqv 'b szero))]]
    (function/lam
     [['hab (seqv (smul 'a 'b) szero)]]
     (use-disj (seqv 'a szero) (seqv 'b szero) falsity (mult-zero-split 'a 'b 'hab)
               (function/lam [['za (seqv 'a szero)]] (app 'ha 'za))
               (function/lam [['zb (seqv 'b szero)]] (app 'hb 'zb)))))})

(def theorem-specs [multiply-zero-split-spec multiply-nonzero-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      mdz/extend-environment
      identities/extend-environment
      action-scale/extend-environment
      equivalence-laws/extend-environment
      (support/extend-with :signed-multiply-nonzero theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
