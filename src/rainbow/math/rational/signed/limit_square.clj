(ns rainbow.math.rational.signed.limit-square
  "A direct corollary of analysis/limit-product: the square of a convergent signed
  sequence converges to the square of the limit.

    analysis/limit-square : converges s L Ms -> converges (n |-> (s n)*(s n)) (L*L) M'

  M' is limit-product's own modulus instantiated at t=s, M=L, Mt=Ms. The proof is the
  single application `limit-product s s L L Ms Ms convS convS`. This is the degree-2 case
  of the (existentially-moduled) limit-power induction; the general limit-power (positive
  powers, by Nat.rec on the exponent using limit-product at each step, with an
  existential modulus to avoid modulus-matching) is the natural next extension. Axiom-free;
  additive; does not touch the LP checker; does NOT depend on the reciprocal arc."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-product :as limit-product]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-seq (function/arrow nat signed))
(def ^:private modulus (function/arrow signed nat))
(def ^:private one (function/const* 'signed/one []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- mk [num dp] (app (function/const* 'data/pair [tl tl]) nat nat num dp))
(defn- recip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))
;; limit-product's modulus (copied): V=(1+|L|)+|M|, d eps = (from-nnrat(recip mmag))*eps
(defn- mmag-of [L M] (let [D (mag (sadd (sadd one (abs* L)) (abs* M)))]
                       (mk (succ (pred* (numr D))) (denpred D))))
(defn- d-of [L M eps] (smul (fnn (recip (mmag-of L M))) eps))
(defn- Mprime [L M Ms Mt]
  (function/lam [['eps signed]]
                (nadd (nadd (app Ms (d-of L M 'eps)) (app Mt (d-of L M 'eps)))
                      (app Ms one))))
(defn- limit-product-app [s t L M Ms Mt convS convT]
  (app (function/const* 'analysis/limit-product []) s t L M Ms Mt convS convT))

(def limit-square-spec
  {:name 'analysis/limit-square
   :universes []
   :type (function/forall
          [['s sig-seq] ['L signed] ['Ms modulus] ['convS (converges 's 'L 'Ms)]]
          (converges (function/lam [['n nat]] (smul (app 's 'n) (app 's 'n)))
                     (smul 'L 'L)
                     (Mprime 'L 'L 'Ms 'Ms)))
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['Ms modulus] ['convS (converges 's 'L 'Ms)]]
    (limit-product-app 's 's 'L 'L 'Ms 'Ms 'convS 'convS))})

(def theorem-specs [limit-square-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      limit-product/extend-environment
      (support/extend-with :signed-limit-square theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
