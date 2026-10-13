(ns rainbow.math.rational.nnrat.distributive
  "Right-distributivity of nonnegative-rational multiplication over addition, up to
  nnrat equivalence:

      multiply-distributes-add-right : (a + b) * m  ~  a*m + b*m     (all a b m)

  This is the last algebra brick for the convex-combination bound.  The proof is the
  first real payoff of the nat-ring tactic (rainbow.math.nat.ring): nnrat/equivalent
  unfolds to a nat cross-product equality numL*denR = numR*denL whose two sides are
  degree-7 monomial sums that agree only after full semiring reordering.  We

    1. transport the packed product-denominators succ(combine ..) to product form
       (da*dm etc.) with the nnrat/denominator-combine law + congruence,
    2. discharge the resulting pure product/sum identity with nat-ring/prove-nat-eq
       (which normalizes both sides to a canonical sum of monomials),
    3. transport the denominators back on the other side.

  Native and axiom-free; chains rainbow.math.nat.ring and nonnegative-rational (d63)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def successor (function/const* 'data/succ []))

(defn- nsucc [v] (function/app successor v))
(def ^:private nmul ring/nmul)
(def ^:private nadd ring/nadd)
(defn- rnum [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))

;; combine law as a proof record: succ(combine l r) = (succ l)*(succ r)
(defn- cl [l r]
  {:lhs (nsucc (combine l r)) :rhs (nmul (nsucc l) (nsucc r))
   :proof (function/app (function/const* 'nnrat/denominator-combine []) l r)})

(def multiply-distributes-add-right-spec
  {:name 'nnrat/multiply-distributes-add-right :universes []
   :type (function/forall
          [['a nnrat] ['b nnrat] ['m nnrat]]
          (equiv (rmul (radd 'a 'b) 'm) (radd (rmul 'a 'm) (rmul 'b 'm))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['m nnrat]]
    (let [na (rnum 'a) nb (rnum 'b) nm (rnum 'm)
          dpa (dpre 'a) dpb (dpre 'b) dpm (dpre 'm)
          da (nsucc dpa) db (nsucc dpb) dm (nsucc dpm)
          ;; reduced goal endpoints (equivalent unfolds to eq-nat(numL*denR)(numR*denL))
          num-l (nmul (nadd (nmul na db) (nmul nb da)) nm)
          den-r-packed (nsucc (combine (combine dpa dpm) (combine dpb dpm)))
          den-l-packed (nsucc (combine (combine dpa dpb) dpm))
          num-r-packed (nadd (nmul (nmul na nm) (nsucc (combine dpb dpm)))
                             (nmul (nmul nb nm) (nsucc (combine dpa dpm))))
          ;; product-denominator forms
          den-r-prod (nmul (nmul da dm) (nmul db dm))
          den-l-prod (nmul (nmul da db) dm)
          num-r-prod (nadd (nmul (nmul na nm) (nmul db dm))
                           (nmul (nmul nb nm) (nmul da dm)))
          pl (nmul num-l den-r-prod)
          pr (nmul num-r-prod den-l-prod)
          ;; den-r-packed = den-r-prod
          pf-den-r (ring/chain* [(cl (combine dpa dpm) (combine dpb dpm))
                                 (ring/cong-mul-left (nsucc (combine dpb dpm)) (cl dpa dpm))
                                 (ring/cong-mul-right (nmul da dm) (cl dpb dpm))])
          ;; den-l-packed = den-l-prod
          pf-den-l (ring/chain* [(cl (combine dpa dpb) dpm)
                                 (ring/cong-mul-left dm (cl dpa dpb))])
          ;; num-r-prod = num-r-packed
          s1r (ring/cong-mul-right (nmul na nm) (ring/symp (cl dpb dpm)))
          s2r (ring/cong-mul-right (nmul nb nm) (ring/symp (cl dpa dpm)))
          pf-num-r (ring/chain (ring/cong-add-left (nmul (nmul nb nm) (nmul da dm)) s1r)
                               (ring/cong-add-right (:rhs s1r) s2r))
          ;; Goal-LHS = PL ; PL = PR ; PR = Goal-RHS
          transport-l (ring/cong-mul-right num-l pf-den-r)
          ring-step (ring/prove-nat-eq pl pr)
          transport-r (ring/chain (ring/cong-mul-right num-r-prod (ring/symp pf-den-l))
                                  (ring/cong-mul-left den-l-packed pf-num-r))]
      (:proof (ring/chain* [transport-l ring-step transport-r]))))})

;; 1 * x ~ x.  nnrat/one = 1/1, so num(1*x) reduces to (natOne * nx) and den(1*x) to the
;; packed succ(combine 0 dpx); after transporting that to natOne*dx via the combine law,
;; equivalence is the pure reordering (natOne*nx)*dx = nx*(natOne*dx) -- natOne is just an
;; opaque atom to the ring tactic, so no numeric one-law is needed.
(def multiply-one-left-spec
  (let [zero-nat (function/const* 'data/zero [])
        one-nat (nsucc zero-nat)
        rone (function/const* 'nnrat/one [])]
    {:name 'nnrat/multiply-one-left :universes []
     :type (function/forall [['x nnrat]] (equiv (rmul rone 'x) 'x))
     :value
     (function/lam
      [['x nnrat]]
      (let [nx (rnum 'x) dpx (dpre 'x) dx (nsucc dpx)
            goal-lhs (nmul (nmul one-nat nx) dx)
            pr' (nmul nx (nmul one-nat dx))
            ring-step (ring/prove-nat-eq goal-lhs pr')
            transport-back (ring/cong-mul-right nx (ring/symp (cl zero-nat dpx)))]
        (:proof (ring/chain ring-step transport-back))))}))

(def definition-specs [])
(def theorem-specs [multiply-distributes-add-right-spec multiply-one-left-spec])

(defn extend-environment [checked-environment]
  ;; shared: nnrat/multiply-one-left is also installed by nnrat-identities
  (support/extend-with-shared checked-environment :nnrat-distributive
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
