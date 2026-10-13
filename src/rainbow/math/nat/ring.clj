(ns rainbow.math.nat.ring
  "A verified nat-semiring normalization tactic: Clojure metaprograms that EMIT
  kernel-checkable equality proof-terms for expressions built from nat/multiply and
  algebra/nat-add.  Rather than hand-writing fragile four-reorder chains, callers build
  proofs by normalization -- reduce each side to a canonical polynomial form and chain
  the atomic semiring laws (associativity, commutativity, distributivity) through
  congruence + transitivity.

  This file is a TACTIC LIBRARY, not a spec module: it exports functions that return
  either a raw proof term or a proof-record {:lhs :rhs :proof} where :proof : lhs = rhs.
  It operates on SURFACE terms (built with function/const* using the alias symbols
  'nat/multiply and 'algebra/nat-add), before elaboration.

  Phase 1 (this commit): PRODUCT (monomial) normalization -- prove any two products of
  the same multiset of nat factors equal, generalizing nat/multiply-four-reorder to
  arbitrary arity.  Phases 2/3 (sums, distribution) build on this."
  (:require [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))

;; ---- surface-term builders --------------------------------------------------
(defn nmul [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn nadd [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- eq-nat [l r] (function/equality type-level nat l r))

;; ---- equality-proof primitives ---------------------------------------------
(defn- refl [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- sym [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- trans [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- cong [lam l r p]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat lam l r p))
(defn- mul-assoc [l m r]      ; (l*m)*r = l*(m*r)
  (function/app (function/const* 'nat/multiply-associative []) l m r))
(defn- mul-comm [l r]         ; l*r = r*l
  (function/app (function/const* 'nat/multiply-commutative []) l r))

;; ---- proof records: {:lhs a :rhs b :proof (p : a = b)} ---------------------
(defn reflp [t] {:lhs t :rhs t :proof (refl t)})
(defn chain [p q]
  (when-not (= (:rhs p) (:lhs q))
    (throw (ex-info "nat-ring chain endpoint mismatch"
                    {:p-rhs (:rhs p) :q-lhs (:lhs q)})))
  {:lhs (:lhs p) :rhs (:rhs q)
   :proof (trans (:lhs p) (:rhs p) (:rhs q) (:proof p) (:proof q))})
(defn chain* [ps] (reduce chain ps))
(defn symp [p]
  {:lhs (:rhs p) :rhs (:lhs p) :proof (sym (:lhs p) (:rhs p) (:proof p))})

;; congruence in the two multiplicative holes; 'ring-hole cannot occur in nat exprs
(defn cong-mul-left [r p]     ; a=b  |-  a*r = b*r
  {:lhs (nmul (:lhs p) r) :rhs (nmul (:rhs p) r)
   :proof (cong (function/lam [['ring-hole nat]] (nmul 'ring-hole r))
                (:lhs p) (:rhs p) (:proof p))})
(defn cong-mul-right [l p]    ; a=b  |-  l*a = l*b
  {:lhs (nmul l (:lhs p)) :rhs (nmul l (:rhs p))
   :proof (cong (function/lam [['ring-hole nat]] (nmul l 'ring-hole))
                (:lhs p) (:rhs p) (:proof p))})

;; ---- product model ---------------------------------------------------------
(defn- mul-node? [t]
  (and (vector? t) (= :app (first t))
       (= (function/const* 'nat/multiply []) (second t))
       (= 4 (count t))))
(defn- mul-l [t] (nth t 2))
(defn- mul-r [t] (nth t 3))

(defn- fold-prod [atoms]      ; nonempty seq -> right-nested product
  (let [atoms (vec atoms)]
    (if (= 1 (count atoms))
      (first atoms)
      (nmul (first atoms) (fold-prod (next atoms))))))

;; prove-concat: mul (fold-prod la)(fold-prod ra) = fold-prod (la ++ ra)  (both nonempty)
(defn- prove-concat [la ra]
  (let [la (vec la) fp-ra (fold-prod ra)]
    (if (= 1 (count la))
      (reflp (nmul (first la) fp-ra))
      (let [a (first la) rest (vec (next la))
            fp-rest (fold-prod rest)
            assocp {:lhs (nmul (nmul a fp-rest) fp-ra)
                    :rhs (nmul a (nmul fp-rest fp-ra))
                    :proof (mul-assoc a fp-rest fp-ra)}
            innerp (cong-mul-right a (prove-concat rest ra))]
        (chain assocp innerp)))))

;; flatten a product term into [atoms, {:lhs t :rhs (fold-prod atoms)}]
(defn- flatten-prod [t]
  (if (mul-node? t)
    (let [[la pa] (flatten-prod (mul-l t))
          [ra pb] (flatten-prod (mul-r t))
          step1 (chain (cong-mul-left (mul-r t) pa)
                       (cong-mul-right (fold-prod la) pb))
          atoms (into (vec la) ra)]
      [atoms (chain step1 (prove-concat la ra))])
    [[t] (reflp t)]))

;; swap-head2: mul a (mul b X) = mul b (mul a X)
(defn- swap-head2 [a b x]
  (chain* [{:lhs (nmul a (nmul b x)) :rhs (nmul (nmul a b) x)
            :proof (sym (nmul (nmul a b) x) (nmul a (nmul b x)) (mul-assoc a b x))}
           (cong-mul-left x {:lhs (nmul a b) :rhs (nmul b a) :proof (mul-comm a b)})
           {:lhs (nmul (nmul b a) x) :rhs (nmul b (nmul a x))
            :proof (mul-assoc b a x)}]))

(defn- atom-key [t] (pr-str t))

;; insert a into sorted vector; returns [new-sorted {:lhs (fp (cons a sorted)) :rhs (fp new-sorted)}]
(defn- insert-prod [a sorted]
  (cond
    (empty? sorted) [[a] (reflp a)]
    (<= (compare (atom-key a) (atom-key (first sorted))) 0)
    (let [new (into [a] sorted)] [new (reflp (fold-prod new))])
    :else
    (let [b (first sorted) rest (vec (next sorted))
          [ins pins] (insert-prod a rest)]     ; pins : fp(a:rest) = fp ins
      (if (empty? rest)
        ;; fp(a:[b]) = mul a b ; fp(b:ins) where ins=[a] -> mul b a
        [(into [b] ins)
         {:lhs (nmul a b) :rhs (nmul b a) :proof (mul-comm a b)}]
        (let [swp (swap-head2 a b (fold-prod rest))   ; mul a (mul b R) = mul b (mul a R)
              lift (cong-mul-right b pins)]            ; mul b (fp(a:rest)) = mul b (fp ins)
          [(into [b] ins) (chain swp lift)])))))

;; sort a product's atoms; returns [sorted {:lhs (fp atoms) :rhs (fp sorted)}]
(defn- sort-prod [atoms]
  (let [atoms (vec atoms)]
    (if (<= (count atoms) 1)
      [atoms (reflp (fold-prod atoms))]
      (let [a (first atoms) rest (vec (next atoms))
            [srest prest] (sort-prod rest)         ; fp rest = fp srest
            congp (cong-mul-right a prest)          ; mul a (fp rest) = mul a (fp srest)
            [ins pins] (insert-prod a srest)]       ; fp(a:srest) = fp ins
        [ins (chain congp pins)]))))

;; normalize a product term -> {:lhs t :rhs canon :atoms sorted-atoms :proof ...}
(defn normalize-prod [t]
  (let [[atoms fp-proof] (flatten-prod t)
        [sorted sort-proof] (sort-prod atoms)]
    (assoc (chain fp-proof sort-proof) :atoms sorted)))

;; PUBLIC: prove two product terms equal (throws if not equal as multisets of atoms)
(defn prove-product-eq [a b]
  (let [na (normalize-prod a) nb (normalize-prod b)]
    (when-not (= (:atoms na) (:atoms nb))
      (throw (ex-info "nat-ring: products differ as atom multisets"
                      {:a (:atoms na) :b (:atoms nb)})))
    (chain na (symp nb))))

;; ============================================================================
;; Phase 2/3: additive layer + distribution -> full sum-of-monomials normalizer
;; ============================================================================

(defn- add-node? [t]
  (and (vector? t) (= :app (first t))
       (= (function/const* 'algebra/nat-add []) (second t))
       (= 4 (count t))))
(defn- add-l [t] (nth t 2))
(defn- add-r [t] (nth t 3))

(defn- add-assoc [l m r]      ; (l+m)+r = l+(m+r)
  (function/app (function/const* 'nat/add-associative []) l m r))
(defn- add-comm [l r]         ; l+r = r+l
  (function/app (function/const* 'nat/add-commutative []) l r))
(defn- dist-right [l r f]     ; (l+r)*f = l*f + r*f   (the only distributivity in d63)
  (function/app (function/const* 'nat/multiply-add-left []) l r f))

(defn cong-add-left [r p]     ; a=b |- a+r = b+r
  {:lhs (nadd (:lhs p) r) :rhs (nadd (:rhs p) r)
   :proof (cong (function/lam [['ring-hole nat]] (nadd 'ring-hole r))
                (:lhs p) (:rhs p) (:proof p))})
(defn cong-add-right [l p]    ; a=b |- l+a = l+b
  {:lhs (nadd l (:lhs p)) :rhs (nadd l (:rhs p))
   :proof (cong (function/lam [['ring-hole nat]] (nadd l 'ring-hole))
                (:lhs p) (:rhs p) (:proof p))})

(defn- fold-sum [terms]
  (let [v (vec terms)]
    (if (= 1 (count v)) (first v) (nadd (first v) (fold-sum (next v))))))

(defn- swap-head2-add [a b x]  ; a+(b+x) = b+(a+x)
  (chain* [{:lhs (nadd a (nadd b x)) :rhs (nadd (nadd a b) x)
            :proof (sym (nadd (nadd a b) x) (nadd a (nadd b x)) (add-assoc a b x))}
           (cong-add-left x {:lhs (nadd a b) :rhs (nadd b a) :proof (add-comm a b)})
           {:lhs (nadd (nadd b a) x) :rhs (nadd b (nadd a x))
            :proof (add-assoc b a x)}]))

;; add (fold-sum la)(fold-sum ra) = fold-sum (la ++ ra)   (both nonempty)
(defn- prove-concat-sum [la ra]
  (let [la (vec la) fs-ra (fold-sum ra)]
    (if (= 1 (count la))
      (reflp (nadd (first la) fs-ra))
      (let [a (first la) rest (vec (next la))
            fs-rest (fold-sum rest)
            assocp {:lhs (nadd (nadd a fs-rest) fs-ra)
                    :rhs (nadd a (nadd fs-rest fs-ra))
                    :proof (add-assoc a fs-rest fs-ra)}
            innerp (cong-add-right a (prove-concat-sum rest ra))]
        (chain assocp innerp)))))

;; flatten a sum term into [summands, {:lhs t :rhs (fold-sum summands)}]
(defn- flatten-sum [t]
  (if (add-node? t)
    (let [[la pa] (flatten-sum (add-l t))
          [ra pb] (flatten-sum (add-r t))
          step1 (chain (cong-add-left (add-r t) pa)
                       (cong-add-right (fold-sum la) pb))
          summands (into (vec la) ra)]
      [summands (chain step1 (prove-concat-sum la ra))])
    [[t] (reflp t)]))

;; insertion sort of monomials; elements are [term key]; sort by (pr-str key)
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
           {:lhs (nadd ta tb) :rhs (nadd tb ta) :proof (add-comm ta tb)}]
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
          drp {:lhs (nmul A B) :rhs (nadd (nmul a1 B) (nmul a2 B))
               :proof (dist-right a1 a2 B)}
          p1 (distribute a1 B) p2 (distribute a2 B)]
      (chain drp (chain (cong-add-left (nmul a2 B) p1)
                        (cong-add-right (:rhs p1) p2))))
    (add-node? B)
    (let [b1 (add-l B) b2 (add-r B)
          ;; left-distribution derived from right-distribution + commutativity:
          ;; A*(b1+b2) = (b1+b2)*A = b1*A + b2*A = A*b1 + A*b2
          dlp (chain* [{:lhs (nmul A B) :rhs (nmul B A) :proof (mul-comm A B)}
                       {:lhs (nmul B A) :rhs (nadd (nmul b1 A) (nmul b2 A))
                        :proof (dist-right b1 b2 A)}
                       (cong-add-left (nmul b2 A)
                                      {:lhs (nmul b1 A) :rhs (nmul A b1)
                                       :proof (mul-comm b1 A)})
                       (cong-add-right (nmul A b1)
                                       {:lhs (nmul b2 A) :rhs (nmul A b2)
                                        :proof (mul-comm b2 A)})])
          p1 (distribute A b1) p2 (distribute A b2)]
      (chain dlp (chain (cong-add-left (nmul A b2) p1)
                        (cong-add-right (:rhs p1) p2))))
    :else (reflp (nmul A B))))

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

;; rewrite each summand to its canonical product: fold-sum lhss = fold-sum rhss
(defn- rewrite-summands [normed]
  (let [normed (vec normed)]
    (if (= 1 (count normed))
      (first normed)
      (let [p1 (first normed) rest (vec (next normed))
            congp (cong-add-left (fold-sum (map :lhs rest)) p1)
            liftp (cong-add-right (:rhs p1) (rewrite-summands rest))]
        (chain congp liftp)))))

;; normalize any nat expression to a sorted sum of canonical monomials
(defn normalize-sum [t]
  (let [ep (expand t)
        [summands fsp] (flatten-sum (:rhs ep))
        normed (mapv normalize-prod summands)
        persum (rewrite-summands normed)
        pairs (mapv (fn [n] [(:rhs n) (:atoms n)]) normed)
        [sorted sortp] (sort-sum pairs)]
    (assoc (chain* [ep fsp persum sortp])
           :monos (mapv second sorted))))

;; PUBLIC: prove two nat semiring expressions equal (coefficient-free: equal iff same
;; multiset of monomials). Throws if they are not semiring-equal, so no false proof.
(defn prove-nat-eq [a b]
  (let [na (normalize-sum a) nb (normalize-sum b)]
    (when-not (= (:monos na) (:monos nb))
      (throw (ex-info "nat-ring: expressions differ as monomial multisets"
                      {:a (:monos na) :b (:monos nb)})))
    (chain na (symp nb))))
