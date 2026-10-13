(ns rainbow.math.rational.signed.limit-product
  "The product limit law: the pointwise product of two convergent signed-rational
  sequences converges to the product of the limits. This is the capstone of the
  real-analysis limit-product arc. Axiom-free; additive.

    analysis/limit-product :
      converges s L Ms -> converges t M Mt ->
      converges (n |-> (s n) * (t n)) (L * M) M'

  with modulus  M' eps = nadd (nadd (Ms (d eps)) (Mt (d eps))) (Ms one)
  and scaled radius  d eps = (from-nnrat (recip mmag)) * eps,
  where V = (1+|L|)+|M|, D = magnitude V, mmag = make (succ (pred (num D))) (den-pred D).

  The radius (B*(d eps) + |M|*(d eps)) produced by close-product collapses to eps:
  distributivity gathers it to V*(d eps), from-nnrat-magnitude replaces V by from-nnrat D
  (V is nonnegative -- product-radius-nonneg), and nnrat-radius-cancel cancels the reciprocal
  (num D is positive -- product-radius-numerator-positive). Threshold extraction and the final
  close-respects-radius-equivalence follow the analysis/limit-sum template exactly."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.close-product :as close-product]
            [rainbow.math.rational.signed.convergent-bounded :as convergent-bounded]
            [rainbow.math.rational.signed.limit-arithmetic :as limit-arithmetic]
            [rainbow.math.rational.nnrat.radius-cancel :as radius-cancel]
            [rainbow.math.rational.signed.product-radius-nonneg :as radius-nonneg]
            [rainbow.math.rational.signed.product-radius-positive :as radius-positive]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-seq (function/arrow nat signed))
(def ^:private modulus (function/arrow signed nat))
(def ^:private one (function/const* 'signed/one []))
(def ^:private zero (function/const* 'data/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- recip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- mk [num dp] (app (function/const* 'data/pair [tl tl]) nat nat num dp))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [x y] (function/equality tl nat x y))
(defn- refl-nat [x] (app (function/const* 'equality/reflexive [tl]) nat x))
(defn- add-comm [a b] (app (function/const* 'nat/add-commutative []) a b))
(defn- nat-trans [a b c ab bc] (app (function/const* 'nat/at-most-transitive []) a b c ab bc))
(defn- witness-nat [pred value proof]
  (app (function/const* 'proposition/witness [tl]) nat pred value proof))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))
;; signed / analysis theorem wrappers
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- distributes [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- fnn-magn [x h] (app (function/const* 'signed/from-nnrat-magnitude []) x h))
(defn- radius-nn [L M] (app (function/const* 'analysis/product-radius-nonneg []) L M))
(defn- radius-pos [L M] (app (function/const* 'analysis/product-radius-numerator-positive []) L M))
(defn- nrc [D eps h] (app (function/const* 'analysis/nnrat-radius-cancel []) D eps h))
(defn- conv-bounded [s L Ms conv n hn]
  (app (function/const* 'analysis/convergent-bounded []) s L Ms conv n hn))
(defn- close-prod [x y L M es et B hLx hMy hxB]
  (app (function/const* 'analysis/close-product []) x y L M es et B hLx hMy hxB))
(defn- close-resp [L eps epsp x same bounded]
  (app (function/const* 'analysis/close-respects-radius-equivalence []) L eps epsp x same bounded))

;; V = (1+|L|)+|M| ; D = magnitude V ; mmag = make(succ(pred(num D)))(den-pred D)
(defn- V-of [L M] (sadd (sadd one (abs* L)) (abs* M)))
(defn- D-of [L M] (mag (V-of L M)))
(defn- mmag-of [L M] (let [D (D-of L M)] (mk (succ (pred* (numr D))) (denpred D))))
(defn- d-of [L M eps] (smul (fnn (recip (mmag-of L M))) eps))
(defn- Mprime [L M Ms Mt]
  (function/lam [['eps signed]]
                (nadd (nadd (app Ms (d-of L M 'eps)) (app Mt (d-of L M 'eps)))
                      (app Ms one))))

(def limit-product-spec
  {:name 'analysis/limit-product
   :universes []
   :type
   (function/forall
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['convS (converges 's 'L 'Ms)] ['convT (converges 't 'M 'Mt)]]
    (converges (function/lam [['n nat]] (smul (app 's 'n) (app 't 'n)))
               (smul 'L 'M)
               (Mprime 'L 'M 'Ms 'Mt)))
   :value
   (function/lam
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['convS (converges 's 'L 'Ms)] ['convT (converges 't 'M 'Mt)]]
    (let [B (sadd one (abs* 'L))
          V (V-of 'L 'M)
          D (D-of 'L 'M)]
      (function/lam
       [['eps signed] ['n nat]
        ['large (nat-le (app (Mprime 'L 'M 'Ms 'Mt) 'eps) 'n)]]
       (let [deps (d-of 'L 'M 'eps)
             A (app 'Ms deps)            ; Ms (d eps)
             Bb (app 'Mt deps)           ; Mt (d eps)
             C (app 'Ms one)             ; Ms one
             P (nadd A Bb)
             thr (nadd P C)              ; = M' eps
             ;; --- threshold split (limit-sum template) ---
             P<=thr (witness-nat (function/lam [['x nat]] (eq-nat (nadd P 'x) thr))
                                 C (refl-nat thr))
             C<=thr (witness-nat (function/lam [['x nat]] (eq-nat (nadd C 'x) thr))
                                 P (add-comm C P))
             P<=n (nat-trans P thr 'n P<=thr 'large)
             C<=n (nat-trans C thr 'n C<=thr 'large)
             A<=P (witness-nat (function/lam [['x nat]] (eq-nat (nadd A 'x) P))
                               Bb (refl-nat P))
             Bb<=P (witness-nat (function/lam [['x nat]] (eq-nat (nadd Bb 'x) P))
                                A (add-comm Bb A))
             A<=n (nat-trans A P 'n A<=P P<=n)
             Bb<=n (nat-trans Bb P 'n Bb<=P P<=n)
             ;; --- pointwise facts ---
             sn (app 's 'n) tn (app 't 'n)
             cS (app 'convS deps 'n A<=n)                       ; close L (d eps) (s n)
             cT (app 'convT deps 'n Bb<=n)                      ; close M (d eps) (t n)
             bnd (conv-bounded 's 'L 'Ms 'convS 'n C<=n)        ; sle (abs (s n)) B
             cp (close-prod sn tn 'L 'M deps deps B cS cT bnd)  ; close (L*M) radius (s n * t n)
             radius (sadd (smul B deps) (smul (abs* 'M) deps))
             ;; --- radius collapse: radius ~ eps ---
             dist (distributes B (abs* 'M) deps)                ; smul V deps ~ radius
             t1 (eqv-sym (smul V deps) radius dist)             ; radius ~ smul V deps
             magEq (fnn-magn V (radius-nn 'L 'M))               ; V ~ from-nnrat D
             t2 (mrre V (fnn D) deps magEq)                     ; smul V deps ~ smul (fnn D) deps
             t3 (nrc D 'eps (radius-pos 'L 'M))                 ; smul (fnn D) deps ~ eps
             radius-eps (eqv-tr radius (smul V deps) 'eps
                                t1 (eqv-tr (smul V deps) (smul (fnn D) deps) 'eps t2 t3))]
         (close-resp (smul 'L 'M) radius 'eps (smul sn tn) radius-eps cp)))))})

(def theorem-specs [limit-product-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      close-product/extend-environment
      convergent-bounded/extend-environment
      limit-arithmetic/extend-environment
      radius-cancel/extend-environment
      radius-nonneg/extend-environment
      radius-positive/extend-environment
      distributive/extend-environment
      equivalence-laws/extend-environment
      (support/extend-with :signed-limit-product theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
