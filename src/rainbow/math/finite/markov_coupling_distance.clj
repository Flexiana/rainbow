(ns rainbow.math.finite.markov-coupling-distance
  "Off-diagonal kernel-row distance bound from a coupling's two marginals.

  A nonnegative joint mass J with marginals p,q proves
  L1(pK,qK) <= sum_i sum_j J(i,j)*L1(K(i,-),K(j,-)).
  No stochastic normalization is needed. The marginal hypotheses are
  algebraic identities, not the desired distance bound."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-residual-coupling :as coupling]
            [rainbow.math.rational.nnrat.weighted-map-sum-distance :as weighted]
            [rainbow.math.rational.nnrat.fubini :as fubini]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat coupling/nnrat)
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- dist [a b] (app 'nnrat/distance a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- items [] (poly 'finset-data/enumeration 'S 'states))
(defn- sum [mapping] (poly 'nnrat/map-sum 'S mapping (items)))
(defn- same-sum [a b pointwise]
  (poly 'nnrat/map-sum-respects-equivalence 'S a b pointwise (items)))
(defn- swap-sums [mapping]
  (poly 'nnrat/map-sum-swap 'S 'S mapping (items) (items)))
(defn- step [mass] (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
(defn- l1 [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
(defn- joint [i j] (f/app 'joint i j))
(defn- entry [i t] (f/app 'kernel i t))
(defn- row-marginal [i] (sum (f/lam [['j 'S]] (joint i 'j))))
(defn- col-marginal [j] (sum (f/lam [['i 'S]] (joint 'i j))))
(def bindings
  (into coupling/base-binders
        [['kernel (f/arrow 'S 'S nnrat)] ['joint (f/arrow 'S 'S nnrat)]
         ['left-marginal (f/forall [['i 'S]] (eqv (row-marginal 'i) (f/app 'left 'i)))]
         ['right-marginal (f/forall [['j 'S]] (eqv (col-marginal 'j) (f/app 'right 'j)))]]))

(defn- projected [left? t]
  (sum (f/lam [['i 'S]]
         (sum (f/lam [['j 'S]]
                (mul (joint 'i 'j) (entry (if left? 'i 'j) t)))))))

(defn- project-left [t]
  (let [before (f/lam [['i 'S]] (mul (f/app 'left 'i) (entry 'i t)))
        after (f/lam [['i 'S]]
                (sum (f/lam [['j 'S]] (mul (joint 'i 'j) (entry 'i t)))))]
    (same-sum before after
      (f/lam [['i 'S]]
        (trans (f/app before 'i) (mul (row-marginal 'i) (entry 'i t)) (f/app after 'i)
               (app 'nnrat/multiply-respects-equivalence
                    (f/app 'left 'i) (row-marginal 'i) (entry 'i t) (entry 'i t)
                    (sym (row-marginal 'i) (f/app 'left 'i) (f/app 'left-marginal 'i))
                    (refl (entry 'i t)))
               (poly 'nnrat/map-sum-scale-right 'S
                     (f/lam [['j 'S]] (joint 'i 'j)) (entry 'i t) (items)))))))

(defn- project-right [t]
  (let [before (f/lam [['j 'S]] (mul (f/app 'right 'j) (entry 'j t)))
        after (f/lam [['j 'S]]
                (sum (f/lam [['i 'S]] (mul (joint 'i 'j) (entry 'j t)))))]
    (trans (f/app (step 'right) t) (sum after) (projected false t)
           (same-sum before after
             (f/lam [['j 'S]]
               (trans (f/app before 'j) (mul (col-marginal 'j) (entry 'j t)) (f/app after 'j)
                      (app 'nnrat/multiply-respects-equivalence
                           (f/app 'right 'j) (col-marginal 'j) (entry 'j t) (entry 'j t)
                           (sym (col-marginal 'j) (f/app 'right 'j) (f/app 'right-marginal 'j))
                           (refl (entry 'j t)))
                      (poly 'nnrat/map-sum-scale-right 'S
                            (f/lam [['i 'S]] (joint 'i 'j)) (entry 'j t) (items)))))
           (swap-sums (f/lam [['j 'S] ['i 'S]] (mul (joint 'i 'j) (entry 'j t)))))))

(defn- cost [i j t] (mul (joint i j) (dist (entry i t) (entry j t))))
(defn- target-cost [t]
  (sum (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (cost 'i 'j t))))))

(defn- projected-distance-bound [t]
  (let [left (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (mul (joint 'i 'j) (entry 'i t)))))
        right (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (mul (joint 'i 'j) (entry 'j t)))))
        radii (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (cost 'i 'j t))))]
    (poly 'nnrat/map-sum-distance-bound-by 'S left right radii
          (f/lam [['i 'S]]
            (poly 'nnrat/weighted-map-sum-distance-bound 'S
                  (f/lam [['j 'S]] (entry 'i t))
                  (f/lam [['j 'S]] (entry 'j t))
                  (f/lam [['j 'S]] (joint 'i 'j)) (items)))
          (items))))

(defn- pair-cost [i j] (mul (joint i j) (l1 (f/app 'kernel i) (f/app 'kernel j))))
(defn- factor-target-sum [i j]
  (let [mapping (f/lam [['t 'S]] (dist (entry i 't) (entry j 't)))
        before (f/lam [['t 'S]] (cost i j 't))
        ordered (f/lam [['t 'S]] (mul (f/app mapping 't) (joint i j)))
        scaled (mul (sum mapping) (joint i j))]
    (trans (sum before) (sum ordered) (pair-cost i j)
           (same-sum before ordered
             (f/lam [['t 'S]]
               (app 'nnrat/multiply-commutative (joint i j) (f/app mapping 't))))
           (trans (sum ordered) scaled (pair-cost i j)
                  (sym scaled (sum ordered)
                       (poly 'nnrat/map-sum-scale-right 'S mapping (joint i j) (items)))
                  (app 'nnrat/multiply-commutative (sum mapping) (joint i j))))))

(defn- aggregate-cost []
  (sum (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (pair-cost 'i 'j))))))
(defn- cost-reorder []
  (let [target-first (sum (f/lam [['t 'S]] (target-cost 't)))
        i-first (f/lam [['i 'S]]
                  (sum (f/lam [['t 'S]] (sum (f/lam [['j 'S]] (cost 'i 'j 't))))))
        pair-first (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (pair-cost 'i 'j))))]
    (trans target-first (sum i-first) (aggregate-cost)
           (swap-sums (f/lam [['t 'S] ['i 'S]]
                        (sum (f/lam [['j 'S]] (cost 'i 'j 't)))))
           (same-sum i-first pair-first
             (f/lam [['i 'S]]
               (let [j-first (f/lam [['j 'S]] (sum (f/lam [['t 'S]] (cost 'i 'j 't))))
                     j-cost (f/lam [['j 'S]] (pair-cost 'i 'j))]
                 (trans (f/app i-first 'i) (sum j-first) (f/app pair-first 'i)
                        (swap-sums (f/lam [['t 'S] ['j 'S]] (cost 'i 'j 't)))
                        (same-sum j-first j-cost (f/lam [['j 'S]] (factor-target-sum 'i 'j))))))))))

(def coupling-distance-bound-spec
  (let [left (f/lam [['t 'S]] (projected true 't))
        right (f/lam [['t 'S]] (projected false 't))
        lhs (l1 (step 'left) (step 'right))
        raw-map (f/lam [['t 'S]] (target-cost 't))
        distances (f/lam [['t 'S]] (dist (f/app left 't) (f/app right 't)))]
    {:name 'markov/nnrat-kernel-step-coupling-distance-bound :universes ['u]
     :type (f/forall bindings (le lhs (aggregate-cost)))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-respects-equivalence
            lhs (l1 left right) (aggregate-cost) (sum raw-map)
            (poly 'markov/nnrat-total-variation-respects-pointwise-equivalent
                  'S 'states (step 'left) left (step 'right) right
                  (f/lam [['t 'S]] (project-left 't))
                  (f/lam [['t 'S]] (project-right 't)))
            (sym (sum raw-map) (aggregate-cost) (cost-reorder))
            (poly 'nnrat/map-sum-monotone 'S distances raw-map
                  (f/lam [['t 'S]] (projected-distance-bound 't)) (items))))}))

(defn- total [mapping] (poly 'probability/nnrat-total-mass 'S 'states mapping))
(defn- positive-mass [] (app 'nnrat/make (app 'data/succ 'ap) 'adp))
(def positive-residual-binders
  (into coupling/base-binders
        [['kernel (f/arrow 'S 'S nnrat)] ['ap coupling/nat] ['adp coupling/nat]
         ['same-total (eqv (total 'left) (total 'right))]
         ['positive-residual-total
          (eqv (total (coupling/residual-mapping :left)) (positive-mass))]]))
(defn- residual-joint []
  (poly 'markov/nnrat-product-coupling 'S 'states
        (coupling/residual-mapping :left) (coupling/residual-mapping :right) (positive-mass)))
(defn- residual-pair-cost []
  (sum (f/lam [['i 'S]]
         (sum (f/lam [['j 'S]]
                (mul (f/app (residual-joint) 'i 'j)
                     (l1 (f/app 'kernel 'i) (f/app 'kernel 'j))))))))
(defn- right-residual-total []
  (let [p (total (coupling/residual-mapping :left))
        q (total (coupling/residual-mapping :right))]
    (trans q p (positive-mass)
           (sym p q (poly 'markov/nnrat-residual-totals-equal 'S 'states 'left 'right 'same-total))
           'positive-residual-total)))

(def positive-residual-coupling-bound-spec
  (let [p (coupling/residual-mapping :left) q (coupling/residual-mapping :right)
        lhs (l1 (step 'left) (step 'right))
        rhs (residual-pair-cost)]
    {:name 'markov/nnrat-kernel-step-positive-residual-coupling-bound :universes ['u]
     :type (f/forall positive-residual-binders (le lhs rhs))
     :value
     (f/lam positive-residual-binders
       (app 'nnrat/at-most-respects-equivalence lhs (l1 (step p) (step q)) rhs rhs
            (poly 'markov/nnrat-kernel-step-total-variation-residual
                  'S 'states 'kernel 'left 'right)
            (refl rhs)
            (poly 'markov/nnrat-kernel-step-coupling-distance-bound
                  'S 'states p q 'kernel (residual-joint)
                  (f/lam [['i 'S]]
                    (poly 'markov/nnrat-product-coupling-left-marginal
                          'S 'states p q 'ap 'adp (right-residual-total) 'i))
                  (f/lam [['j 'S]]
                    (poly 'markov/nnrat-product-coupling-right-marginal
                          'S 'states p q 'ap 'adp 'positive-residual-total 'j)))))}))

(def residual-coupling-total-spec
  (let [p (coupling/residual-mapping :left) q (coupling/residual-mapping :right)
        rows (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (f/app (residual-joint) 'i 'j))))]
    {:name 'markov/nnrat-positive-residual-coupling-total :universes ['u]
     :type (f/forall positive-residual-binders (eqv (sum rows) (positive-mass)))
     :value
     (f/lam positive-residual-binders
       (trans (sum rows) (total p) (positive-mass)
              (same-sum rows p
                (f/lam [['i 'S]]
                  (poly 'markov/nnrat-product-coupling-left-marginal
                        'S 'states p q 'ap 'adp (right-residual-total) 'i)))
              'positive-residual-total))}))

(def theorem-specs [coupling-distance-bound-spec positive-residual-coupling-bound-spec
                    residual-coupling-total-spec])
(defn extend-environment [env]
  (-> env coupling/extend-environment weighted/extend-environment
      ((fn [e] (if (environment/resolve-id e 'nnrat/map-sum-swap) e
                 (support/add-spec e :finite-markov-coupling-distance-support fubini/map-sum-swap-spec))))
      (support/extend-with :finite-markov-coupling-distance theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
