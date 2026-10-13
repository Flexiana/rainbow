(ns rainbow.math.rational.signed.multiply-order
  "The sign rules for signed-rational multiplication.

  Until now the signed layer had no order lemma about `signed/multiply` at all:
  the order toolkit was purely additive.  The obstruction is real -- a signed
  product mixes the four component products

      positive (a*b) = Pa*Pb + Na*Nb,    negative (a*b) = Pa*Nb + Na*Pb

  and no amount of termwise monotonicity relates those two sums, because moving
  one factor up moves one summand up and the other down.  The two-point
  rearrangement inequality is exactly the missing fact, and once it is available
  each sign rule is a single instantiation:

      nonneg a, nonneg b  =>  nonneg (a*b)      [n,p,q,m := Na,Pa,Nb,Pb]
      nonneg a, nonpos b  =>  nonpos (a*b)      [n,p,q,m := Na,Pa,Pb,Nb]
      nonpos a, nonpos b  =>  nonneg (a*b)      [n,p,q,m := Pa,Na,Pb,Nb]

  `signed/nonnegative v` is already the codebase's zero-free predicate
  `negative v <= positive v`; this module adds the mirrored `signed/nonpositive`
  and four bridges identifying both with the order comparisons against
  `signed/zero`, so the sign rules can be used wherever the Lagrangian and
  optimality modules speak of `0 <= x` and `x <= 0`.

  This is what a concrete Lagrangian penalty needs: a nonnegative multiplier
  times a satisfied (nonpositive) constraint is nonpositive.

  Native and axiom-free; chains signed multiplication and the nnrat
  rearrangement toolkit on D63.  The two additive-identity equivalences are
  rebuilt here as local proof terms rather than chained from
  rainbow.math.rational.nnrat.identities, because that module and
  rainbow.math.rational.nnrat.distributive (which the rearrangement toolkit needs) both
  declare `nnrat/multiply-one-left`, and chaining two providers of one alias is
  a kernel alias conflict."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-difference :as difference]
            [rainbow.math.rational.signed.multiply :as multiply]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- rat-le [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- nonneg [v] (app (function/const* 'signed/nonnegative []) v))
(defn- nonpos [v] (app (function/const* 'signed/nonpositive []) v))

(defn- rat-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
;; ---- local additive-identity equivalences ----------------------------------
;;
;; (X + 0) ~ X and (0 + X) ~ X, built from the nat identity laws exactly as
;; rainbow.math.rational.nnrat.identities builds them, but emitted inline so no second
;; provider of any alias is introduced.

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nat-one (app (function/const* 'data/succ []) nat-zero))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- nsucc [v] (app (function/const* 'data/succ []) v))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- rnum [v] (app (function/const* 'nnrat/numerator []) v))
(defn- rden [v] (app (function/const* 'nnrat/denominator []) v))
(defn- rdpre [v] (app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [a b]
  (app (function/const* 'nnrat/combine-denominator-predecessors []) a b))

(defn- nat-refl [v]
  (app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- nat-sym [a b same]
  (app (function/const* 'equality/symmetric [type-level]) nat a b same))
(defn- nat-trans [a b c first second]
  (app (function/const* 'equality/transitive [type-level]) nat a b c first second))
(defn- nat-cong [mapping a b same]
  (app (function/const* 'equality/congruent-function [type-level type-level])
       nat nat mapping a b same))

(defn- denominator-with-right-one [value]
  (let [dp (rdpre value)]
    (nat-trans (nsucc (combine dp nat-zero))
               (nmul (nsucc dp) nat-one)
               (rden value)
               (app (function/const* 'nnrat/denominator-combine [])
                    dp nat-zero)
               (app (function/const* 'nat/multiply-one-right []) (nsucc dp)))))

(defn- denominator-with-left-one [value]
  (let [dp (rdpre value)]
    (nat-trans (nsucc (combine nat-zero dp))
               (nmul nat-one (nsucc dp))
               (rden value)
               (app (function/const* 'nnrat/denominator-combine [])
                    nat-zero dp)
               (app (function/const* 'nat/one-times []) (nsucc dp)))))

(defn- zero-times [value]
  (nat-trans (nmul nat-zero value) (nmul value nat-zero) nat-zero
             (app (function/const* 'nat/multiply-commutative []) nat-zero value)
             (app (function/const* 'nat/times-zero []) value)))

(defn- rat-add-zero-right [value]
  (let [n (rnum value)
        d (rden value)
        result (radd value nnrat-zero)
        result-numerator (rnum result)
        result-denominator (rden result)
        numerator-same
        (nat-trans (nadd (nmul n nat-one) nat-zero) (nmul n nat-one) n
                   (app (function/const* 'algebra/nat-add-zero-right [])
                        (nmul n nat-one))
                   (app (function/const* 'nat/multiply-one-right []) n))
        denominator-same (denominator-with-right-one value)]
    (nat-trans
     (nmul result-numerator d) (nmul n d) (nmul n result-denominator)
     (nat-cong (function/lam [['candidate nat]] (nmul 'candidate d))
               result-numerator n numerator-same)
     (nat-sym (nmul n result-denominator) (nmul n d)
              (nat-cong (function/lam [['candidate nat]] (nmul n 'candidate))
                        result-denominator d denominator-same)))))

(defn- rat-add-zero-left [value]
  (let [n (rnum value)
        d (rden value)
        result (radd nnrat-zero value)
        result-numerator (rnum result)
        result-denominator (rden result)
        n-times-one (nmul n nat-one)
        numerator-same
        (nat-trans
         (nadd (nmul nat-zero d) n-times-one) (nadd nat-zero n-times-one) n
         (nat-cong (function/lam [['candidate nat]]
                                 (nadd 'candidate n-times-one))
                   (nmul nat-zero d) nat-zero (zero-times d))
         (nat-trans (nadd nat-zero n-times-one) n-times-one n
                    (nat-refl n-times-one)
                    (app (function/const* 'nat/multiply-one-right []) n)))
        denominator-same (denominator-with-left-one value)]
    (nat-trans
     (nmul result-numerator d) (nmul n d) (nmul n result-denominator)
     (nat-cong (function/lam [['candidate nat]] (nmul 'candidate d))
               result-numerator n numerator-same)
     (nat-sym (nmul n result-denominator) (nmul n d)
              (nat-cong (function/lam [['candidate nat]] (nmul n 'candidate))
                        result-denominator d denominator-same)))))
(defn- rearrange [n p q m hnp hqm]
  (app (function/const* 'nnrat/rearrangement-two-point []) n p q m hnp hqm))

;; The mirror of signed/nonnegative: the negative part dominates.
(def nonpositive-spec
  {:name 'signed/nonpositive :kind :definition :universes []
   :type (function/arrow signed 'Prop)
   :value (function/lam [['value signed]]
                        (rat-le (pos 'value) (neg 'value)))})

;; ---- sign rules -------------------------------------------------------------

(def multiply-nonnegative-spec
  {:name 'signed/multiply-nonnegative :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['ha (nonneg 'a)] ['hb (nonneg 'b)]]
          (nonneg (smul 'a 'b)))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ha (nonneg 'a)] ['hb (nonneg 'b)]]
    ;; goal: Pa*Nb + Na*Pb <= Pa*Pb + Na*Nb
    (rearrange (neg 'a) (pos 'a) (neg 'b) (pos 'b) 'ha 'hb))})

(def multiply-nonnegative-nonpositive-spec
  {:name 'signed/multiply-nonnegative-nonpositive :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['ha (nonneg 'a)] ['hb (nonpos 'b)]]
          (nonpos (smul 'a 'b)))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ha (nonneg 'a)] ['hb (nonpos 'b)]]
    ;; goal: Pa*Pb + Na*Nb <= Pa*Nb + Na*Pb
    (rearrange (neg 'a) (pos 'a) (pos 'b) (neg 'b) 'ha 'hb))})

(def multiply-nonpositive-spec
  {:name 'signed/multiply-nonpositive :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['ha (nonpos 'a)] ['hb (nonpos 'b)]]
          (nonneg (smul 'a 'b)))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ha (nonpos 'a)] ['hb (nonpos 'b)]]
    (let [PaPb (rmul (pos 'a) (pos 'b))
          NaNb (rmul (neg 'a) (neg 'b))
          PaNb (rmul (pos 'a) (neg 'b))
          NaPb (rmul (neg 'a) (pos 'b))]
      ;; rearrangement gives Na*Pb + Pa*Nb <= Na*Nb + Pa*Pb; the goal is the
      ;; same comparison with both sums written the other way round.
      (rat-at-most-respects
       (radd PaNb NaPb) (radd NaPb PaNb)
       (radd PaPb NaNb) (radd NaNb PaPb)
       (rat-comm PaNb NaPb) (rat-comm PaPb NaNb)
       (rearrange (pos 'a) (neg 'a) (pos 'b) (neg 'b) 'ha 'hb))))})

;; ---- bridges to the comparisons against signed/zero -------------------------
;;
;; `signed/zero` has both components zero, so `x <= 0` unfolds to
;; (Px + 0) <= (0 + Nx) and `0 <= x` to (0 + Nx) <= (Px + 0).  The identity laws
;; strip the paddings in either direction.

(def at-most-zero-of-nonpositive-spec
  {:name 'signed/at-most-zero-of-nonpositive :universes []
   :type (function/forall
          [['x signed] ['hx (nonpos 'x)]]
          (sle 'x signed-zero))
   :value
   (function/lam
    [['x signed] ['hx (nonpos 'x)]]
    (rat-at-most-respects
     (radd (pos 'x) (neg signed-zero)) (pos 'x)
     (radd (pos signed-zero) (neg 'x)) (neg 'x)
     (rat-add-zero-right (pos 'x))
     (rat-add-zero-left (neg 'x))
     'hx))})

(def nonpositive-of-at-most-zero-spec
  {:name 'signed/nonpositive-of-at-most-zero :universes []
   :type (function/forall
          [['x signed] ['hx (sle 'x signed-zero)]]
          (nonpos 'x))
   :value
   (function/lam
    [['x signed] ['hx (sle 'x signed-zero)]]
    (rat-at-most-respects
     (pos 'x) (radd (pos 'x) (neg signed-zero))
     (neg 'x) (radd (pos signed-zero) (neg 'x))
     (rat-sym (radd (pos 'x) (neg signed-zero)) (pos 'x)
              (rat-add-zero-right (pos 'x)))
     (rat-sym (radd (pos signed-zero) (neg 'x)) (neg 'x)
              (rat-add-zero-left (neg 'x)))
     'hx))})

(def zero-at-most-of-nonnegative-spec
  {:name 'signed/zero-at-most-of-nonnegative :universes []
   :type (function/forall
          [['x signed] ['hx (nonneg 'x)]]
          (sle signed-zero 'x))
   :value
   (function/lam
    [['x signed] ['hx (nonneg 'x)]]
    (rat-at-most-respects
     (radd (pos signed-zero) (neg 'x)) (neg 'x)
     (radd (pos 'x) (neg signed-zero)) (pos 'x)
     (rat-add-zero-left (neg 'x))
     (rat-add-zero-right (pos 'x))
     'hx))})

(def nonnegative-of-zero-at-most-spec
  {:name 'signed/nonnegative-of-zero-at-most :universes []
   :type (function/forall
          [['x signed] ['hx (sle signed-zero 'x)]]
          (nonneg 'x))
   :value
   (function/lam
    [['x signed] ['hx (sle signed-zero 'x)]]
    (rat-at-most-respects
     (neg 'x) (radd (pos signed-zero) (neg 'x))
     (pos 'x) (radd (pos 'x) (neg signed-zero))
     (rat-sym (radd (pos signed-zero) (neg 'x)) (neg 'x)
              (rat-add-zero-left (neg 'x)))
     (rat-sym (radd (pos 'x) (neg signed-zero)) (pos 'x)
              (rat-add-zero-right (pos 'x)))
     'hx))})

;; The headline corollary in the shape the Lagrangian modules use: a nonnegative
;; multiplier times a satisfied constraint contributes a nonpositive penalty.
(def multiplier-times-satisfied-constraint-spec
  {:name 'optimization/signed-multiplier-penalty-nonpositive :universes []
   :type (function/forall
          [['lambda signed] ['g signed]
           ['hlambda (sle signed-zero 'lambda)]
           ['hg (sle 'g signed-zero)]]
          (sle (smul 'lambda 'g) signed-zero))
   :value
   (function/lam
    [['lambda signed] ['g signed]
     ['hlambda (sle signed-zero 'lambda)]
     ['hg (sle 'g signed-zero)]]
    (app (function/const* 'signed/at-most-zero-of-nonpositive [])
         (smul 'lambda 'g)
         (app (function/const* 'signed/multiply-nonnegative-nonpositive [])
              'lambda 'g
              (app (function/const* 'signed/nonnegative-of-zero-at-most [])
                   'lambda 'hlambda)
              (app (function/const* 'signed/nonpositive-of-at-most-zero [])
                   'g 'hg))))})

(def definition-specs [nonpositive-spec])
(def theorem-specs
  [multiply-nonnegative-spec
   multiply-nonnegative-nonpositive-spec
   multiply-nonpositive-spec
   at-most-zero-of-nonpositive-spec
   nonpositive-of-at-most-zero-spec
   zero-at-most-of-nonnegative-spec
   nonnegative-of-zero-at-most-spec
   multiplier-times-satisfied-constraint-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.order-difference])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-multiply-order (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.multiply-order))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
