(ns rainbow.math.rational.signed.multiply-ring
  "Signed multiplication is commutative and well defined on the Grothendieck
  quotient.

    signed/multiply-commutative                a*b ~ b*a
    signed/multiply-left-respects-equivalence  b~b' -> c*b ~ c*b'
    signed/multiply-right-respects-equivalence a~a' -> a*c ~ a'*c
    signed/multiply-respects-equivalence       a~a' -> b~b' -> a*b ~ a'*b'
    signed/multiply-zero-right                 a*0 ~ 0

  Well-definedness is the one that matters: a signed rational is a PAIR, and
  `signed/equivalent` is a quotient relation on pairs, so until multiplication is
  shown to respect it, no signed product may be rewritten under an equivalence --
  which blocks every reassociation inside a weighted sum.

  Commutativity and the zero law are pure semiring identities on the four
  component products, so each is a single `rainbow.math.rational.nnrat.ring` call.  The
  one-sided congruence is the only proof with real content: it factors the fixed
  factor OUT of the four component products,

      (Pc*Pb + Nc*Nb) + (Pc*Nb' + Nc*Pb')  ~  (Pb + Nb')*Pc + (Nb + Pb')*Nc

  -- itself a ring identity -- at which point the hypothesis `Pb + Nb' ~ Pb' + Nb`
  rewrites both of those sums to the same thing.  The other side of the goal
  factors to the identical expression, so the two meet in the middle.  The
  right-hand and two-sided versions then follow by commutativity and
  `signed/equivalent-transitive`.

  Native and axiom-free; chains the nnrat-ring tactic and the signed finite-sum
  algebra (for signed equivalence transitivity) on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.map-sum-algebra :as algebra]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(def ^:private radd ring/radd)
(def ^:private rmul ring/rmul)
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
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
(defn- rat-mul-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       a ah b bh same-a same-b))

(defn- signed-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))

;; the two Grothendieck components of a signed product
(defn- product-positive [pl nl pr nr] (radd (rmul pl pr) (rmul nl nr)))
(defn- product-negative [pl nl pr nr] (radd (rmul pl nr) (rmul nl pr)))

;; ---- commutativity -----------------------------------------------------------

(def multiply-commutative-spec
  {:name 'signed/multiply-commutative :universes []
   :type (function/forall
          [['a signed] ['b signed]]
          (seq-equiv (smul 'a 'b) (smul 'b 'a)))
   :value
   (function/lam
    [['a signed] ['b signed]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b)]
      (ring/equiv (radd (product-positive Pa Na Pb Nb)
                        (product-negative Pb Nb Pa Na))
                  (radd (product-positive Pb Nb Pa Na)
                        (product-negative Pa Na Pb Nb)))))})

;; ---- one-sided congruence ----------------------------------------------------

;; rewrite both factored sums to the common (target)*Pc + (target)*Nc
(defn- retarget [Pc Nc u w v z target first-same second-same]
  (rat-add-respects (rmul (radd u w) Pc) (rmul target Pc)
                    (rmul (radd v z) Nc) (rmul target Nc)
                    (rat-mul-respects (radd u w) target Pc Pc
                                      first-same (rat-refl Pc))
                    (rat-mul-respects (radd v z) target Nc Nc
                                      second-same (rat-refl Nc))))

(def multiply-left-respects-spec
  {:name 'signed/multiply-left-respects-equivalence :universes []
   :type (function/forall
          [['b signed] ['bh signed] ['c signed]
           ['same (seq-equiv 'b 'bh)]]
          (seq-equiv (smul 'c 'b) (smul 'c 'bh)))
   :value
   (function/lam
    [['b signed] ['bh signed] ['c signed]
     ['same (seq-equiv 'b 'bh)]]
    (let [Pc (pos 'c) Nc (neg 'c)
          Pb (pos 'b) Nb (neg 'b) Pbh (pos 'bh) Nbh (neg 'bh)
          target (radd Pbh Nb)
          left (radd (product-positive Pc Nc Pb Nb)
                     (product-negative Pc Nc Pbh Nbh))
          left-factored (radd (rmul (radd Pb Nbh) Pc) (rmul (radd Nb Pbh) Nc))
          right (radd (product-positive Pc Nc Pbh Nbh)
                      (product-negative Pc Nc Pb Nb))
          right-factored (radd (rmul (radd Pbh Nb) Pc) (rmul (radd Nbh Pb) Nc))
          meeting (radd (rmul target Pc) (rmul target Nc))
          left-meet
          (rat-trans
           left left-factored meeting
           (ring/equiv left left-factored)
           (retarget Pc Nc Pb Nbh Nb Pbh target 'same (rat-comm Nb Pbh)))
          right-meet
          (rat-trans
           right right-factored meeting
           (ring/equiv right right-factored)
           (retarget Pc Nc Pbh Nb Nbh Pb target
                     (rat-refl target)
                     (rat-trans (radd Nbh Pb) (radd Pb Nbh) target
                                (rat-comm Nbh Pb) 'same)))]
      (rat-trans left meeting right
                 left-meet
                 (rat-sym right meeting right-meet))))})

(def multiply-right-respects-spec
  {:name 'signed/multiply-right-respects-equivalence :universes []
   :type (function/forall
          [['a signed] ['ah signed] ['c signed]
           ['same (seq-equiv 'a 'ah)]]
          (seq-equiv (smul 'a 'c) (smul 'ah 'c)))
   :value
   (function/lam
    [['a signed] ['ah signed] ['c signed]
     ['same (seq-equiv 'a 'ah)]]
    (signed-trans
     (smul 'a 'c) (smul 'c 'a) (smul 'ah 'c)
     (app (function/const* 'signed/multiply-commutative []) 'a 'c)
     (signed-trans
      (smul 'c 'a) (smul 'c 'ah) (smul 'ah 'c)
      (app (function/const* 'signed/multiply-left-respects-equivalence [])
           'a 'ah 'c 'same)
      (app (function/const* 'signed/multiply-commutative []) 'c 'ah))))})

(def multiply-respects-spec
  {:name 'signed/multiply-respects-equivalence :universes []
   :type (function/forall
          [['a signed] ['ah signed] ['b signed] ['bh signed]
           ['same-a (seq-equiv 'a 'ah)] ['same-b (seq-equiv 'b 'bh)]]
          (seq-equiv (smul 'a 'b) (smul 'ah 'bh)))
   :value
   (function/lam
    [['a signed] ['ah signed] ['b signed] ['bh signed]
     ['same-a (seq-equiv 'a 'ah)] ['same-b (seq-equiv 'b 'bh)]]
    (signed-trans
     (smul 'a 'b) (smul 'ah 'b) (smul 'ah 'bh)
     (app (function/const* 'signed/multiply-right-respects-equivalence [])
          'a 'ah 'b 'same-a)
     (app (function/const* 'signed/multiply-left-respects-equivalence [])
          'b 'bh 'ah 'same-b)))})

;; a*0 has identical components, so the pair is equivalent to zero -- with the
;; zero treated as one more opaque atom, that too is a ring identity.
(def multiply-zero-right-spec
  {:name 'signed/multiply-zero-right :universes []
   :type (function/forall [['a signed]]
                          (seq-equiv (smul 'a signed-zero) signed-zero))
   :value
   (function/lam
    [['a signed]]
    (let [component (radd (rmul (pos 'a) nnrat-zero) (rmul (neg 'a) nnrat-zero))]
      (ring/equiv (radd component nnrat-zero) (radd nnrat-zero component))))})

(def definition-specs [])
(def theorem-specs
  [multiply-commutative-spec
   multiply-left-respects-spec
   multiply-right-respects-spec
   multiply-respects-spec
   multiply-zero-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ring/extend-environment
      algebra/extend-environment
      (support/extend-with :signed-multiply-ring theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
