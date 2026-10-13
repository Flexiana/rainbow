(ns rainbow.math.rational.nnrat.ring
  "A verified nonnegative-rational semiring normalization tactic, up to
  `nnrat/equivalent`.

  This is the `rainbow.math.nat.ring` analogue one level up.  Where nat-ring
  normalizes expressions over `algebra/nat-add` / `nat/multiply` and chains
  PROPOSITIONAL EQUALITIES, this file normalizes expressions over `nnrat/add` /
  `nnrat/multiply` and chains NNRAT EQUIVALENCES -- because nnrat addition and
  multiplication are associative, commutative and distributive only up to `~`
  (a sum's denominator depends on how it was bracketed), so no reassociation of
  an nnrat expression is ever a definitional equality.

  That distinction is the whole reason this exists.  Hand-writing a signed or
  rational reassociation means chaining `add-four-reorder`, `add-associative`,
  `multiply-commutative` and the two congruence lemmas by hand, and the chains
  grow super-linearly in the number of monomials: the eight-monomial identity
  behind `signed/multiply-associative` is roughly two hundred error-prone lines
  written out. Normalizing both sides to a canonical sorted sum of canonical
  monomials makes it one call.

  Like nat-ring this is a TACTIC LIBRARY, not a spec module: it exports Clojure
  functions returning either a raw proof term or a proof record
  `{:lhs :rhs :proof}` where `:proof : lhs ~ rhs`.  It operates on SURFACE terms
  (built with `function/const*` on the alias symbols `nnrat/add` and
  `nnrat/multiply`), before elaboration.

  PUBLIC ENTRY POINTS
    (prove-equiv a b)   -> proof record; :proof inhabits `nnrat/equivalent a b`.
                           Throws if the two sides are not semiring-equal, so it
                           can never emit a false proof.
    (equiv a b)         -> just the proof term.
    (prove-product-equiv a b) -> the product-only (monomial) special case.
    extend-environment  -> chains every law provider the emitted proofs cite.

  LAWS CITED (all must be in the environment; `extend-environment` puts them
  there): `nnrat/equivalent-reflexive`, `-symmetric`, `-transitive`,
  `nnrat/add-respects-equivalence`, `nnrat/multiply-respects-equivalence`
  (these five are D63 base), `nnrat/add-associative`, `nnrat/add-commutative`,
  `nnrat/multiply-associative`, `nnrat/multiply-commutative`,
  `nnrat/multiply-distributes-add-right`.

  Note the distributive law available is the RIGHT one only; left distribution is
  derived here from it plus multiplicative commutativity, exactly as nat-ring
  does.  The distribute-right provider is `nnrat-distribute-right` rather than
  `nnrat-distributive`, so that consumers of this tactic remain compatible with
  `nnrat-identities` (the two full modules both declare
  `nnrat/multiply-one-left`, and chaining both is an alias conflict)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as dist]
            [rainbow.math.rational.nnrat.multiply-commute :as mul-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as mul-reassoc]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

;; ---- surface-term builders --------------------------------------------------
(defn rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn radd [l r] (function/app (function/const* 'nnrat/add []) l r))

;; ---- equivalence-proof primitives -------------------------------------------
(defn- refl [v]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- sym [l r p]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l lh r rh pl pr]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                l lh r rh pl pr))
(defn- mul-respects [l lh r rh pl pr]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence [])
                l lh r rh pl pr))
(defn- mul-assoc [l m r]      ; (l*m)*r ~ l*(m*r)
  (function/app (function/const* 'nnrat/multiply-associative []) l m r))
(defn- mul-comm [l r]         ; l*r ~ r*l
  (function/app (function/const* 'nnrat/multiply-commutative []) l r))
(defn- add-assoc [l m r]      ; (l+m)+r ~ l+(m+r)
  (function/app (function/const* 'nnrat/add-associative []) l m r))
(defn- add-comm [l r]         ; l+r ~ r+l
  (function/app (function/const* 'nnrat/add-commutative []) l r))
(defn- dist-right [l r f]     ; (l+r)*f ~ l*f + r*f
  (function/app (function/const* 'nnrat/multiply-distributes-add-right [])
                l r f))

;; ---- proof records: {:lhs a :rhs b :proof (p : a ~ b)} ---------------------
(defn reflp [t] {:lhs t :rhs t :proof (refl t)})

(defn chain [p q]
  (when-not (= (:rhs p) (:lhs q))
    (throw (ex-info "nnrat-ring chain endpoint mismatch"
                    {:p-rhs (:rhs p) :q-lhs (:lhs q)})))
  {:lhs (:lhs p) :rhs (:rhs q)
   :proof (trans (:lhs p) (:rhs p) (:rhs q) (:proof p) (:proof q))})

(defn chain* [ps] (reduce chain ps))

(defn symp [p]
  {:lhs (:rhs p) :rhs (:lhs p) :proof (sym (:lhs p) (:rhs p) (:proof p))})

;; Congruence uses the two respects lemmas with reflexivity on the fixed side.
;; Unlike nat-ring there is no `equality/congruent-function` available here --
;; nnrat equivalence is a relation, not an equality type.
(defn cong-mul-left [r p]     ; a~b |- a*r ~ b*r
  {:lhs (rmul (:lhs p) r) :rhs (rmul (:rhs p) r)
   :proof (mul-respects (:lhs p) (:rhs p) r r (:proof p) (refl r))})

(defn cong-mul-right [l p]    ; a~b |- l*a ~ l*b
  {:lhs (rmul l (:lhs p)) :rhs (rmul l (:rhs p))
   :proof (mul-respects l l (:lhs p) (:rhs p) (refl l) (:proof p))})

(defn cong-add-left [r p]     ; a~b |- a+r ~ b+r
  {:lhs (radd (:lhs p) r) :rhs (radd (:rhs p) r)
   :proof (add-respects (:lhs p) (:rhs p) r r (:proof p) (refl r))})

(defn cong-add-right [l p]    ; a~b |- l+a ~ l+b
  {:lhs (radd l (:lhs p)) :rhs (radd l (:rhs p))
   :proof (add-respects l l (:lhs p) (:rhs p) (refl l) (:proof p))})

;; ---- product model ---------------------------------------------------------
(defn- mul-node? [t]
  (and (vector? t) (= :app (first t))
       (= (function/const* 'nnrat/multiply []) (second t))
       (= 4 (count t))))
(defn- mul-l [t] (nth t 2))
(defn- mul-r [t] (nth t 3))

(defn- fold-prod [atoms]      ; nonempty seq -> right-nested product
  (let [atoms (vec atoms)]
    (if (= 1 (count atoms))
      (first atoms)
      (rmul (first atoms) (fold-prod (next atoms))))))

;; mul (fold-prod la) (fold-prod ra) ~ fold-prod (la ++ ra)   (both nonempty)
(defn- prove-concat [la ra]
  (let [la (vec la) fp-ra (fold-prod ra)]
    (if (= 1 (count la))
      (reflp (rmul (first la) fp-ra))
      (let [a (first la) rest (vec (next la))
            fp-rest (fold-prod rest)
            assocp {:lhs (rmul (rmul a fp-rest) fp-ra)
                    :rhs (rmul a (rmul fp-rest fp-ra))
                    :proof (mul-assoc a fp-rest fp-ra)}
            innerp (cong-mul-right a (prove-concat rest ra))]
        (chain assocp innerp)))))

;; flatten a product term into [atoms {:lhs t :rhs (fold-prod atoms)}]
(defn- flatten-prod [t]
  (if (mul-node? t)
    (let [[la pa] (flatten-prod (mul-l t))
          [ra pb] (flatten-prod (mul-r t))
          step1 (chain (cong-mul-left (mul-r t) pa)
                       (cong-mul-right (fold-prod la) pb))
          atoms (into (vec la) ra)]
      [atoms (chain step1 (prove-concat la ra))])
    [[t] (reflp t)]))

;; a * (b * X) ~ b * (a * X)
(defn- swap-head2 [a b x]
  (chain* [{:lhs (rmul a (rmul b x)) :rhs (rmul (rmul a b) x)
            :proof (sym (rmul (rmul a b) x) (rmul a (rmul b x)) (mul-assoc a b x))}
           (cong-mul-left x {:lhs (rmul a b) :rhs (rmul b a) :proof (mul-comm a b)})
           {:lhs (rmul (rmul b a) x) :rhs (rmul b (rmul a x))
            :proof (mul-assoc b a x)}]))

(defn- atom-key [t] (pr-str t))

;; insert a into a sorted atom vector
(defn- insert-prod [a sorted]
  (cond
    (empty? sorted) [[a] (reflp a)]
    (<= (compare (atom-key a) (atom-key (first sorted))) 0)
    (let [new (into [a] sorted)] [new (reflp (fold-prod new))])
    :else
    (let [b (first sorted) rest (vec (next sorted))
          [ins pins] (insert-prod a rest)]
      (if (empty? rest)
        [(into [b] ins)
         {:lhs (rmul a b) :rhs (rmul b a) :proof (mul-comm a b)}]
        (let [swp (swap-head2 a b (fold-prod rest))
              lift (cong-mul-right b pins)]
          [(into [b] ins) (chain swp lift)])))))

(defn- sort-prod [atoms]
  (let [atoms (vec atoms)]
    (if (<= (count atoms) 1)
      [atoms (reflp (fold-prod atoms))]
      (let [a (first atoms) rest (vec (next atoms))
            [srest prest] (sort-prod rest)
            congp (cong-mul-right a prest)
            [ins pins] (insert-prod a srest)]
        [ins (chain congp pins)]))))

;; normalize a product term -> {:lhs t :rhs canon :atoms sorted-atoms :proof ...}
(defn normalize-prod [t]
  (let [[atoms fp-proof] (flatten-prod t)
        [sorted sort-proof] (sort-prod atoms)]
    (assoc (chain fp-proof sort-proof) :atoms sorted)))

;; PUBLIC: prove two product terms equivalent (throws unless equal as multisets)
(defn prove-product-equiv [a b]
  (let [na (normalize-prod a) nb (normalize-prod b)]
    (when-not (= (:atoms na) (:atoms nb))
      (throw (ex-info "nnrat-ring: products differ as atom multisets"
                      {:a (:atoms na) :b (:atoms nb)})))
    (chain na (symp nb))))

;; ---- additive layer + distribution -----------------------------------------
(defn- add-node? [t]
  (and (vector? t) (= :app (first t))
       (= (function/const* 'nnrat/add []) (second t))
       (= 4 (count t))))
(defn- add-l [t] (nth t 2))
(defn- add-r [t] (nth t 3))

(defn- fold-sum [terms]
  (let [v (vec terms)]
    (if (= 1 (count v)) (first v) (radd (first v) (fold-sum (next v))))))

(defn- swap-head2-add [a b x]  ; a+(b+x) ~ b+(a+x)
  (chain* [{:lhs (radd a (radd b x)) :rhs (radd (radd a b) x)
            :proof (sym (radd (radd a b) x) (radd a (radd b x)) (add-assoc a b x))}
           (cong-add-left x {:lhs (radd a b) :rhs (radd b a) :proof (add-comm a b)})
           {:lhs (radd (radd b a) x) :rhs (radd b (radd a x))
            :proof (add-assoc b a x)}]))

(defn- prove-concat-sum [la ra]
  (let [la (vec la) fs-ra (fold-sum ra)]
    (if (= 1 (count la))
      (reflp (radd (first la) fs-ra))
      (let [a (first la) rest (vec (next la))
            fs-rest (fold-sum rest)
            assocp {:lhs (radd (radd a fs-rest) fs-ra)
                    :rhs (radd a (radd fs-rest fs-ra))
                    :proof (add-assoc a fs-rest fs-ra)}
            innerp (cong-add-right a (prove-concat-sum rest ra))]
        (chain assocp innerp)))))

(defn- flatten-sum [t]
  (if (add-node? t)
    (let [[la pa] (flatten-sum (add-l t))
          [ra pb] (flatten-sum (add-r t))
          step1 (chain (cong-add-left (add-r t) pa)
                       (cong-add-right (fold-sum la) pb))
          summands (into (vec la) ra)]
      [summands (chain step1 (prove-concat-sum la ra))])
    [[t] (reflp t)]))

(defn- insert-sum [pair sorted]
  (let [[ta ka] pair]
    (cond
      (empty? sorted) [[pair] (reflp ta)]
      (<= (compare (pr-str ka) (pr-str (second (first sorted)))) 0)
      (let [new (into [pair] sorted)] [new (reflp (fold-sum (map first new)))])
      :else
      (let [[tb _ :as bp] (first sorted) rest (vec (next sorted))
            [ins pins] (insert-sum pair rest)]
        (if (empty? rest)
          [(into [bp] ins)
           {:lhs (radd ta tb) :rhs (radd tb ta) :proof (add-comm ta tb)}]
          (let [swp (swap-head2-add ta tb (fold-sum (map first rest)))
                lift (cong-add-right tb pins)]
            [(into [bp] ins) (chain swp lift)]))))))

(defn- sort-sum [pairs]
  (let [pairs (vec pairs)]
    (if (<= (count pairs) 1)
      [pairs (reflp (fold-sum (map first pairs)))]
      (let [a (first pairs) rest (vec (next pairs))
            [srest prest] (sort-sum rest)
            congp (cong-add-right (first a) prest)
            [ins pins] (insert-sum a srest)]
        [ins (chain congp pins)]))))

;; distribute A*B into a flat sum of products; A,B already expanded
(defn- distribute [A B]
  (cond
    (add-node? A)
    (let [a1 (add-l A) a2 (add-r A)
          drp {:lhs (rmul A B) :rhs (radd (rmul a1 B) (rmul a2 B))
               :proof (dist-right a1 a2 B)}
          p1 (distribute a1 B) p2 (distribute a2 B)]
      (chain drp (chain (cong-add-left (rmul a2 B) p1)
                        (cong-add-right (:rhs p1) p2))))
    (add-node? B)
    (let [b1 (add-l B) b2 (add-r B)
          ;; left distribution from right distribution plus commutativity
          dlp (chain* [{:lhs (rmul A B) :rhs (rmul B A) :proof (mul-comm A B)}
                       {:lhs (rmul B A) :rhs (radd (rmul b1 A) (rmul b2 A))
                        :proof (dist-right b1 b2 A)}
                       (cong-add-left (rmul b2 A)
                                      {:lhs (rmul b1 A) :rhs (rmul A b1)
                                       :proof (mul-comm b1 A)})
                       (cong-add-right (rmul A b1)
                                       {:lhs (rmul b2 A) :rhs (rmul A b2)
                                        :proof (mul-comm b2 A)})])
          p1 (distribute A b1) p2 (distribute A b2)]
      (chain dlp (chain (cong-add-left (rmul A b2) p1)
                        (cong-add-right (:rhs p1) p2))))
    :else (reflp (rmul A B))))

;; push every multiplication inside additions -> flat sum of products
(defn- expand [t]
  (cond
    (add-node? t)
    (let [pl (expand (add-l t)) pr (expand (add-r t))]
      (chain (cong-add-left (add-r t) pl) (cong-add-right (:rhs pl) pr)))
    (mul-node? t)
    (let [pl (expand (mul-l t)) pr (expand (mul-r t))
          step0 (chain (cong-mul-left (mul-r t) pl) (cong-mul-right (:rhs pl) pr))]
      (chain step0 (distribute (:rhs pl) (:rhs pr))))
    :else (reflp t)))

(defn- rewrite-summands [normed]
  (let [normed (vec normed)]
    (if (= 1 (count normed))
      (first normed)
      (let [p1 (first normed) rest (vec (next normed))
            congp (cong-add-left (fold-sum (map :lhs rest)) p1)
            liftp (cong-add-right (:rhs p1) (rewrite-summands rest))]
        (chain congp liftp)))))

;; normalize any nnrat expression to a sorted sum of canonical monomials
(defn normalize-sum [t]
  (let [ep (expand t)
        [summands fsp] (flatten-sum (:rhs ep))
        normed (mapv normalize-prod summands)
        persum (rewrite-summands normed)
        pairs (mapv (fn [n] [(:rhs n) (:atoms n)]) normed)
        [sorted sortp] (sort-sum pairs)]
    (assoc (chain* [ep fsp persum sortp])
           :monos (mapv second sorted))))

;; PUBLIC: prove two nnrat semiring expressions equivalent.  Coefficient-free:
;; equivalent iff the same multiset of monomials, so it throws rather than emit a
;; false proof.
(defn prove-equiv [a b]
  (let [na (normalize-sum a) nb (normalize-sum b)]
    (when-not (= (:monos na) (:monos nb))
      (throw (ex-info "nnrat-ring: expressions differ as monomial multisets"
                      {:a (:monos na) :b (:monos nb)})))
    (chain na (symp nb))))

(defn equiv [a b] (:proof (prove-equiv a b)))

;; Convenience: put every law the emitted proofs cite into the environment.
;; ORDER MATTERS: nnrat-add-monotone supplies `nnrat/add-commutative`, which both
;; nnrat-multiply-commute and nnrat-additive-reassociation cite while building
;; their own specs, and nnrat-multiply-commute must precede
;; nnrat-product-reassociation, which cites `nnrat/multiply-commutative`.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.nnrat.distribute-right])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  checked-environment)

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.ring))
