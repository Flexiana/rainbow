(ns rainbow.math.rational.signed.unit-laws
  "The unit and self-cancellation laws the signed layer was missing.

  Everything about `signed/one` and about `c - c` had to be re-derived by hand at
  every use site, because the signed layer carried no multiplicative identity and
  no self-subtraction law.  All four proofs below are componentwise: a signed
  equivalence `a ~ b` IS the nnrat equivalence `Pa + Nb ~ Pb + Na`, so each one
  reduces to nnrat identity laws applied to the two Grothendieck components.

    signed/multiply-one-left            1 * z ~ z
    signed/subtract-self-equivalent-zero  c - c ~ 0
    signed/subtract-self-nonpositive      c - c <= 0
    signed/zero-at-most-one               0 <= 1
    signed/equivalent-to-at-most          a ~ b -> a <= b

  The last is worth naming: signed order and signed equivalence unfold to the
  nnrat order and nnrat equivalence of the SAME pair of cross sums, so the nnrat
  bridge transports directly, giving the signed one for free.

  Native and axiom-free; chains signed multiplication and the nnrat identity
  and additive-monotonicity laws on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as am]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.signed.multiply :as multiply]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nat-zero (function/const* 'data/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- nsucc [v] (app (function/const* 'data/succ []) v))
(def nat-one (nsucc nat-zero))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))

(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- rnum [v] (app (function/const* 'nnrat/numerator []) v))
(defn- rden [v] (app (function/const* 'nnrat/denominator []) v))
(defn- rat-le [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-refl [v] (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c first second))
(defn- rat-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- rat-equivalent-to-at-most [a b same]
  (app (function/const* 'nnrat/equivalent-to-at-most []) a b same))
(defn- rat-at-most-from-cross [a b ordered]
  (app (function/const* 'nnrat/at-most-from-cross []) a b ordered))
(defn- rat-add-zero-right [v]
  (app (function/const* 'nnrat/add-zero-right []) v))
(defn- rat-add-zero-left [v]
  (app (function/const* 'nnrat/add-zero-left []) v))
(defn- rat-multiply-one-left [v]
  (app (function/const* 'nnrat/multiply-one-left []) v))
(defn- rat-multiply-zero-left [v]
  (app (function/const* 'nnrat/multiply-zero-left []) v))
(defn- nat-refl [v]
  (app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- nat-witness [pred value proof]
  (app (function/const* 'proposition/witness [type-level]) nat pred value proof))

;; a ~ b  ->  a <= b, componentwise: both unfold on the same two cross sums.
(def equivalent-to-at-most-spec
  {:name 'signed/equivalent-to-at-most :universes []
   :type (function/forall
          [['a signed] ['b signed] ['same (seq-equiv 'a 'b)]]
          (sle 'a 'b))
   :value
   (function/lam
    [['a signed] ['b signed] ['same (seq-equiv 'a 'b)]]
    (rat-equivalent-to-at-most (radd (pos 'a) (neg 'b))
                               (radd (pos 'b) (neg 'a))
                               'same))})

;; 1 * z ~ z.  Both components of the product collapse: 1*P + 0*N ~ P and
;; 1*N + 0*P ~ N, so each side of the equivalence becomes Pz + Nz.
(def multiply-one-left-spec
  {:name 'signed/multiply-one-left :universes []
   :type (function/forall
          [['z signed]]
          (seq-equiv (smul signed-one 'z) 'z))
   :value
   (function/lam
    [['z signed]]
    (let [Pz (pos 'z) Nz (neg 'z)
          collapse
          (fn [kept dropped]
            ;; (1*kept + 0*dropped) ~ kept
            (rat-trans (radd (rmul nnrat-one kept) (rmul nnrat-zero dropped))
                       (radd kept nnrat-zero)
                       kept
                       (rat-add-respects (rmul nnrat-one kept) kept
                                         (rmul nnrat-zero dropped) nnrat-zero
                                         (rat-multiply-one-left kept)
                                         (rat-multiply-zero-left dropped))
                       (rat-add-zero-right kept)))
          A (radd (rmul nnrat-one Pz) (rmul nnrat-zero Nz))
          B (radd (rmul nnrat-one Nz) (rmul nnrat-zero Pz))
          middle (radd Pz Nz)
          left-same (rat-add-respects A Pz Nz Nz (collapse Pz Nz) (rat-refl Nz))
          right-same (rat-add-respects Pz Pz B Nz (rat-refl Pz) (collapse Nz Pz))]
      (rat-trans (radd A Nz) middle (radd Pz B)
                 left-same
                 (rat-sym (radd Pz B) middle right-same))))})

;; c - c ~ 0.  The difference is the pair (Pc+Nc, Nc+Pc), and 0 is (0, 0), so the
;; equivalence is ((Pc+Nc) + 0) ~ (0 + (Nc+Pc)) -- padding plus commutativity.
(def subtract-self-equivalent-zero-spec
  {:name 'signed/subtract-self-equivalent-zero :universes []
   :type (function/forall
          [['c signed]]
          (seq-equiv (ssub 'c 'c) signed-zero))
   :value
   (function/lam
    [['c signed]]
    (let [Pc (pos 'c) Nc (neg 'c)
          forward (radd Pc Nc)
          backward (radd Nc Pc)]
      (rat-trans (radd forward nnrat-zero) forward (radd nnrat-zero backward)
                 (rat-add-zero-right forward)
                 (rat-trans forward backward (radd nnrat-zero backward)
                            (rat-comm Pc Nc)
                            (rat-sym (radd nnrat-zero backward) backward
                                     (rat-add-zero-left backward))))))})

(def subtract-self-nonpositive-spec
  {:name 'signed/subtract-self-nonpositive :universes []
   :type (function/forall
          [['c signed]]
          (sle (ssub 'c 'c) signed-zero))
   :value
   (function/lam
    [['c signed]]
    (app (function/const* 'signed/equivalent-to-at-most [])
         (ssub 'c 'c) signed-zero
         (app (function/const* 'signed/subtract-self-equivalent-zero []) 'c)))})

;; 0 <= 1.  Unfolds to (0 + 0) <= (1 + 0) over nnrat; strip both paddings and the
;; remaining nnrat 0 <= 1 is the cross comparison 0*1 <= 1*1, which reduces to
;; nat 0 <= 1 -- witness 1.
(def zero-at-most-one-spec
  {:name 'signed/zero-at-most-one :universes []
   :type (sle signed-zero signed-one)
   :value
   (let [cross-left (nmul (rnum nnrat-zero) (rden nnrat-one))
         cross-right (nmul (rnum nnrat-one) (rden nnrat-zero))
         base (nat-witness
               (function/lam [['extra nat]]
                             (eq-nat (nadd cross-left 'extra) cross-right))
               nat-one
               (nat-refl cross-right))]
     (rat-at-most-respects
      (radd nnrat-zero nnrat-zero) nnrat-zero
      (radd nnrat-one nnrat-zero) nnrat-one
      (rat-add-zero-right nnrat-zero)
      (rat-add-zero-right nnrat-one)
      (rat-at-most-from-cross nnrat-zero nnrat-one base)))})

(def definition-specs [])
(def theorem-specs
  [equivalent-to-at-most-spec
   multiply-one-left-spec
   subtract-self-equivalent-zero-spec
   subtract-self-nonpositive-spec
   zero-at-most-one-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.identities])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-unit-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.unit-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
