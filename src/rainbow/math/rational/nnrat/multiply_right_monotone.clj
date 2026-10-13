(ns rainbow.math.rational.nnrat.multiply-right-monotone
  "Right-factor monotonicity of nnrat multiplication under the rational order:

    nnrat/multiply-right-monotone : a <= b -> (a * c) <= (b * c)

  The mirror of rainbow.math.rational.nnrat.multiply-monotone (left factor).  Same technique:
  the base lemma reduces base(a*c)(b*c) to a nat cross-product, regroups both sides with
  nat/multiply-four-reorder into (na*db)*(nc*dc) <= (nb*da)*(nc*dc), applies
  nat/multiply-RIGHT-monotone to the hypothesis, and transports the packed product
  denominators via the nnrat/denominator-combine law; the full theorem lifts across the
  reflexive-transitive closure nnrat/at-most.

  Needed for factor-comparison results (e.g. gamma <= 1/2 -> gamma*x <= (1/2)*x), which
  generalise contraction convergence beyond the 1/2 rate.
  Native and axiom-free; self-contained on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def successor (function/const* 'data/succ []))

(defn- nsucc [v] (function/app successor v))
(defn- nmul [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- symmetric [l r same]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r same))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- rnum [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- base-le [a b] (function/app (function/const* 'nnrat/base-at-most []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))

;; base: base-at-most a b -> base-at-most (a*c) (b*c)
(def base-spec
  {:name 'nnrat/multiply-right-monotone-base :universes []
   :type (function/forall
          [['a nnrat] ['b nnrat] ['c nnrat] ['h (base-le 'a 'b)]]
          (base-le (rmul 'a 'c) (rmul 'b 'c)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['h (base-le 'a 'b)]]
    (let [na (rnum 'a) nb (rnum 'b) nc (rnum 'c)
          dpa (dpre 'a) dpb (dpre 'b) dpc (dpre 'c)
          da (nsucc dpa) db (nsucc dpb) dc (nsucc dpc)
          NA (nmul na nc) NB (nmul nb nc)       ; num(a*c), num(b*c)
          Q (nmul nc dc)
          DAc (nsucc (combine dpa dpc)) DBc (nsucc (combine dpb dpc))
          lawA (function/app (function/const* 'nnrat/denominator-combine []) dpa dpc)  ; DAc = da*dc
          lawB (function/app (function/const* 'nnrat/denominator-combine []) dpb dpc)  ; DBc = db*dc
          ;; mono : (na*db)*Q <= (nb*da)*Q
          mono (function/app (function/const* 'nat/multiply-right-monotone [])
                             Q (nmul na db) (nmul nb da) 'h)
          fr-a (function/app (function/const* 'nat/multiply-four-reorder []) na nc db dc)  ; NA*(db*dc)=(na*db)*Q
          fr-b (function/app (function/const* 'nat/multiply-four-reorder []) nb nc da dc)  ; NB*(da*dc)=(nb*da)*Q
          ;; step1: rewrite left (na*db)*Q -> NA*(db*dc)
          step1 (rewrite-left (nmul NA (nmul db dc)) (nmul (nmul na db) Q) (nmul (nmul nb da) Q)
                              fr-a mono)
          ;; step2: rewrite left NA*(db*dc) -> NA*DBc
          congB (congruent (function/lam [['v nat]] (nmul NA 'v)) (nmul db dc) DBc
                           (symmetric DBc (nmul db dc) lawB))
          step2 (rewrite-left (nmul NA DBc) (nmul NA (nmul db dc)) (nmul (nmul nb da) Q)
                              congB step1)
          ;; step3: rewrite right (nb*da)*Q -> NB*(da*dc)
          sym-fr-b (symmetric (nmul NB (nmul da dc)) (nmul (nmul nb da) Q) fr-b)
          step3 (rewrite-right (nmul NA DBc) (nmul (nmul nb da) Q) (nmul NB (nmul da dc))
                               sym-fr-b step2)
          ;; step4: rewrite right NB*(da*dc) -> NB*DAc
          congA (congruent (function/lam [['v nat]] (nmul NB 'v)) (nmul da dc) DAc
                           (symmetric DAc (nmul da dc) lawA))
          step4 (rewrite-right (nmul NA DBc) (nmul NB (nmul da dc)) (nmul NB DAc)
                               congA step3)]
      step4))})

;; closure: a <= b -> (a*c) <= (b*c)
(def monotone-spec
  {:name 'nnrat/multiply-right-monotone :universes []
   :type (function/forall
          [['a nnrat] ['b nnrat] ['c nnrat] ['h (rat-le 'a 'b)]]
          (rat-le (rmul 'a 'c) (rmul 'b 'c)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['h (rat-le 'a 'b)]]
    (let [motive (function/lam [['y nnrat]] (rat-le (rmul 'a 'c) (rmul 'y 'c)))
          step (function/lam
                [['before nnrat] ['after nnrat]
                 ['o (base-le 'before 'after)]
                 ['acc (rat-le (rmul 'a 'c) (rmul 'before 'c))]]
                (let [lifted (function/app
                              (function/const* 'nnrat/at-most-from-cross [])
                              (rmul 'before 'c) (rmul 'after 'c)
                              (function/app (function/const* 'nnrat/multiply-right-monotone-base [])
                                            'before 'after 'c 'o))]
                  (function/app (function/const* 'nnrat/at-most-transitive [])
                                (rmul 'a 'c) (rmul 'before 'c) (rmul 'after 'c)
                                'acc lifted)))
          base-case (function/app (function/const* 'nnrat/at-most-reflexive [])
                                  (rmul 'a 'c))]
      (function/app 'h motive step base-case)))})

(def definition-specs [])
(def theorem-specs [base-spec monotone-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-multiply-right-monotone
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
