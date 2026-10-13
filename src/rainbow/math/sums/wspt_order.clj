(ns rainbow.math.sums.wspt-order
  "WSPT order prerequisites. Strictly positive processing times are caller premises.
  This module alone does not prove schedule optimality or permutation semantics."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed call at mul le eqv refl]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.mmck-unique :as cancel]
            [rainbow.math.rational.signed.no-zero-divisors :as nz]
            [rainbow.math.rational.signed.multiply-positive :as positive]
            [rainbow.math.rational.signed.minmax-algebra :as minmax]
            [rainbow.algorithms.proofs.graph.walk-shorten :as shorten]))
(defn lt [x y] (call 'signed/less-than x y))
(defn order [pa wa pb wb] (le (mul wb pa) (mul wa pb)))
(defn- split-order [x y goal reverse-case forward-case]
  (let [bt (f/const* 'data/Bool []) decision (call 'signed/decide-at-most x y)
        eqb (fn [v] (f/equality [:succ [:zero]] bt decision v))]
    (f/app
      (f/app (f/const* 'data/Bool.rec [[:zero]])
        (f/lam [['ws-choice bt]] (f/arrow (eqb 'ws-choice) goal))
        (f/lam [['ws-false (eqb (f/const* 'data/false []))]]
          (reverse-case (call 'signed/decide-at-most-false-reverse x y 'ws-false)))
        (f/lam [['ws-true (eqb (f/const* 'data/true []))]]
          (forward-case (call 'signed/decide-at-most-true-sound x y 'ws-true))) decision)
      (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) bt decision))))
(def reflect-spec
  (s/spec 'signed/multiply-positive-reflects-order
    [['ws-left signed] ['ws-right signed] ['ws-factor signed]
     ['ws-positive (lt s/zero 'ws-factor)]
     ['ws-scaled (le (mul 'ws-left 'ws-factor) (mul 'ws-right 'ws-factor))]]
    (le 'ws-left 'ws-right)
    (split-order 'ws-left 'ws-right (le 'ws-left 'ws-right)
      (fn [reverse-order]
        (call 'signed/equivalent-to-at-most 'ws-left 'ws-right
          (call 'signed/multiply-cancel-positive-right 'ws-left 'ws-right 'ws-factor 'ws-positive
            (call 'signed/at-most-antisymmetric (mul 'ws-left 'ws-factor) (mul 'ws-right 'ws-factor)
              'ws-scaled
              (call 'signed/multiply-right-monotone 'ws-factor 'ws-right 'ws-left
                (call 'signed/less-than-implies-at-most s/zero 'ws-factor 'ws-positive) reverse-order)))))
      identity)))
(def transitive-spec
  (let [pa 'ws-pa wa 'ws-wa pb 'ws-pb wb 'ws-wb pc 'ws-pc wc 'ws-wc
        lhs (mul (mul wc pa) pb) middle (mul (mul wb pa) pc) rhs (mul (mul wa pc) pb)
        first-step (s/le-transport (mul (mul wc pb) pa) lhs (mul (mul wb pc) pa) middle
                     (a/ring-eq (mul (mul wc pb) pa) lhs)
                     (a/ring-eq (mul (mul wb pc) pa) middle)
                     (call 'signed/multiply-right-monotone pa (mul wc pb) (mul wb pc)
                       (call 'signed/less-than-implies-at-most s/zero pa 'ws-hpa) 'ws-bc))
        second-step (s/le-transport middle middle (mul (mul wa pb) pc) rhs
                      (refl middle) (a/ring-eq (mul (mul wa pb) pc) rhs)
                      (call 'signed/multiply-right-monotone pc (mul wb pa) (mul wa pb)
                        (call 'signed/less-than-implies-at-most s/zero pc 'ws-hpc) 'ws-ab))]
    (s/spec 'signed/wspt-cross-order-transitive
      [[pa signed] [wa signed] [pb signed] [wb signed] [pc signed] [wc signed]
       ['ws-hpa (lt s/zero pa)] ['ws-hpb (lt s/zero pb)] ['ws-hpc (lt s/zero pc)]
       ['ws-ab (order pa wa pb wb)] ['ws-bc (order pb wb pc wc)]]
      (order pa wa pc wc)
      (call 'signed/multiply-positive-reflects-order (mul wc pa) (mul wa pc) pb 'ws-hpb
        (call 'signed/at-most-transitive lhs middle rhs first-step second-step)))))
(def min-ordered-spec
  (let [minimum (call 'signed/min 'ws-a 'ws-b)]
    (s/spec 'signed/wspt-min-of-ordered
      [['ws-a signed] ['ws-b signed] ['ws-ab (le 'ws-a 'ws-b)]]
      (eqv minimum 'ws-a)
      (call 'signed/at-most-antisymmetric minimum 'ws-a
        (call 'signed/min-lower-left 'ws-a 'ws-b)
        (call 'signed/at-most-min 'ws-a 'ws-a 'ws-b
          (call 'signed/at-most-reflexive 'ws-a) 'ws-ab)))))
(defn positive-family [P n] (s/all-below n #(lt s/zero (at P %))))
(defn adjacent [P W last-position]
  (s/all-below last-position #(order (at P %) (at W %) (at P (s/succ %)) (at W (s/succ %)))))
(defn nat-le [i j] (call 'nat/at-most i j))
(defn eqn [i j] (f/equality [:succ [:zero]] nat i j))
(defn- nsym [i j h] (f/app (f/const* 'equality/symmetric [[:succ [:zero]]]) nat i j h))
(defn- nsubst [i j h predicate proof]
  (f/app (f/const* 'equality/substitution [[:succ [:zero]]]) nat i j h predicate proof))
(defn- upto-claim [P W last-position]
  (f/forall [['ws-pos (positive-family P (s/succ last-position))]
             ['ws-adj (adjacent P W last-position)]
             ['ws-first nat] ['ws-before (nat-le 'ws-first last-position)]]
    (order (at P 'ws-first) (at W 'ws-first) (at P last-position) (at W last-position))))
(def upto-spec
  (let [P 'ws-times W 'ws-weights
        same (fn [j] (call 'signed/at-most-reflexive (mul (at W j) (at P j))))
        claim (fn [j] (upto-claim P W j))
        goal (fn [i j] (order (at P i) (at W i) (at P j) (at W j)))]
    (s/spec 'signed/wspt-adjacent-order-up-to
      [[P s/family] [W s/family] ['ws-last nat]] (claim 'ws-last)
      (s/induct claim
        (f/lam [['ws-pos (positive-family P (s/succ s/nz))]
                ['ws-adj (adjacent P W s/nz)] ['ws-first nat]
                ['ws-before (nat-le 'ws-first s/nz)]]
          (nsubst s/nz 'ws-first
            (nsym 'ws-first s/nz (call 'nat/equal-zero-of-at-most-zero 'ws-first 'ws-before))
            (f/lam [['ws-replaced nat]] (goal 'ws-replaced s/nz)) (same s/nz)))
        (fn [previous ih]
          (let [last-position (s/succ previous)
                first 'ws-first same-last (eqn first last-position) earlier (s/below first last-position)
                result (goal first last-position)
                restricted-pos (f/lam [['ws-ri nat] ['ws-rib (s/below 'ws-ri (s/succ previous))]]
                                 (at 'ws-pos 'ws-ri (s/weaken 'ws-ri (s/succ previous) 'ws-rib)))
                restricted-adj (f/lam [['ws-ai nat] ['ws-aib (s/below 'ws-ai previous)]]
                                 (at 'ws-adj 'ws-ai (s/weaken 'ws-ai previous 'ws-aib)))]
            (f/lam [['ws-pos (positive-family P (s/succ last-position))]
                    ['ws-adj (adjacent P W last-position)] [first nat]
                    ['ws-before (nat-le first last-position)]]
              (a/cases same-last earlier result (call 'nat/at-most-split first last-position 'ws-before)
                (f/lam [['ws-same same-last]]
                  (nsubst last-position first (nsym first last-position 'ws-same)
                    (f/lam [['ws-replaced nat]] (goal 'ws-replaced last-position)) (same last-position)))
                (f/lam [['ws-earlier earlier]]
                  (call 'signed/wspt-cross-order-transitive
                    (at P first) (at W first) (at P previous) (at W previous)
                    (at P last-position) (at W last-position)
                    (at 'ws-pos first (call 'nat/successor-monotone first last-position 'ws-before))
                    (at 'ws-pos previous (s/weaken previous last-position (s/self-below previous)))
                    (at 'ws-pos last-position (s/self-below last-position))
                    (at ih restricted-pos restricted-adj first
                      (call 'nat/at-most-successor-cancel-local first previous 'ws-earlier))
                    (at 'ws-adj previous (s/self-below previous)))))))) 'ws-last))))
(def pairwise-spec
  (let [P 'ws-times W 'ws-weights q 'ws-count-predecessor n (s/succ q)]
    (s/spec 'signed/wspt-adjacent-implies-pairwise
      [[P s/family] [W s/family] [q nat] ['ws-positive (positive-family P n)]
       ['ws-adjacency (adjacent P W q)] ['ws-i nat] ['ws-j nat]
       ['ws-ij (nat-le 'ws-i 'ws-j)] ['ws-j-bound (s/below 'ws-j n)]]
      (order (at P 'ws-i) (at W 'ws-i) (at P 'ws-j) (at W 'ws-j))
      (call 'signed/wspt-adjacent-order-up-to P W 'ws-j
        (f/lam [['ws-rp nat] ['ws-rpb (s/below 'ws-rp (s/succ 'ws-j))]]
          (at 'ws-positive 'ws-rp
            (call 'nat/at-most-transitive (s/succ 'ws-rp) (s/succ 'ws-j) n 'ws-rpb 'ws-j-bound)))
        (f/lam [['ws-ra nat] ['ws-rab (s/below 'ws-ra 'ws-j)]]
          (at 'ws-adjacency 'ws-ra
            (call 'nat/at-most-transitive (s/succ 'ws-ra) 'ws-j q 'ws-rab
              (call 'nat/at-most-successor-cancel-local 'ws-j q 'ws-j-bound))))
        'ws-i 'ws-ij))))
(def theorem-specs [reflect-spec transitive-spec min-ordered-spec upto-spec pairwise-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (let [env (-> env a/extend-environment nz/extend-environment positive/extend-environment minmax/extend-environment) env (reduce (fn [checked spec] (support/add-spec-shared checked :wspt-cancel-prerequisites spec)) env [cancel/cancel-or-zero-spec cancel/cancel-positive-spec shorten/successor-cancel-spec])] (reduce (fn [checked spec] (println :wspt-order :installing (:name spec)) (flush) (support/add-spec-shared checked :expr-sum-wspt-order spec)) env theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.wspt-order))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
