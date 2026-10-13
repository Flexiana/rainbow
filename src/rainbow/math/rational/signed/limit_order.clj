(ns rainbow.math.rational.signed.limit-order
  "Limits preserve the pointwise order of signed-rational sequences.

  The convergence predicate ranges over every signed radius, including zero.  At
  the common index Ms(0)+Mt(0), zero-radius convergence gives L <= s(n) and
  t(n) <= M after transporting the endpoints through the established signed-zero
  equivalences.  The pointwise hypothesis and signed order transitivity then give
  L <= s(n) <= t(n) <= M.

  Native and axiom-free; chains the D63 convergence/order toolkit through signed
  limit uniqueness (which supplies signed/add-zero-right)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))

(defn- reflexive-nat [v]
  (app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- witness-nat [pred value proof]
  (app (function/const* 'proposition/witness [type-level])
       nat pred value proof))
(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))

(def limit-preserves-order-spec
  {:name 'analysis/limit-preserves-order :universes []
   :type
   (function/forall
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['pointwise
      (function/forall
       [['n nat]]
       (sle (app 's 'n) (app 't 'n)))]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (sle 'L 'M))
   :value
   (function/lam
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['pointwise
      (function/forall
       [['n nat]]
       (sle (app 's 'n) (app 't 'n)))]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (let [ms (app 'Ms signed-zero)
          mt (app 'Mt signed-zero)
          n (nadd ms mt)
          ms<=n
          (witness-nat
           (function/lam [['extra nat]] (eq-nat (nadd ms 'extra) n))
           mt (reflexive-nat n))
          mt<=n
          (witness-nat
           (function/lam [['extra nat]] (eq-nat (nadd mt 'extra) n))
           ms (app (function/const* 'nat/add-commutative []) mt ms))
          sn (app 's n)
          tn (app 't n)
          L-low (ssub 'L signed-zero)
          M-high (sadd 'M signed-zero)
          s-close (app 's-converges signed-zero n ms<=n)
          t-close (app 't-converges signed-zero n mt<=n)
          L-low<=sn
          (prop-left (sle L-low sn) (sle sn (sadd 'L signed-zero)) s-close)
          tn<=M-high
          (prop-right (sle (ssub 'M signed-zero) tn) (sle tn M-high) t-close)
          L-low-eq-L
          (app (function/const* 'signed/add-zero-right []) 'L)
          M-high-eq-M
          (app (function/const* 'signed/add-zero-right []) 'M)
          L<=sn
          (signed-at-most-respects
           L-low 'L sn sn L-low-eq-L (signed-refl sn) L-low<=sn)
          tn<=M
          (signed-at-most-respects
           tn tn M-high 'M (signed-refl tn) M-high-eq-M tn<=M-high)
          L<=tn
          (signed-transitive 'L sn tn L<=sn (app 'pointwise n))]
      (signed-transitive 'L tn 'M L<=tn tn<=M)))})

(def definition-specs [])
(def theorem-specs [limit-preserves-order-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniqueness/extend-environment
      (support/extend-with :signed-limit-order theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
