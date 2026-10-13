(ns rainbow.math.rational.nnrat.farkas-vector-step-covered
  "Covered elimination step (the vacuity fix, consumer migration): one step in
  the held next-variable representation carrying the covering conjunct.

  farkas-vector-step produced a vacuous held-goal EXISTS (l,u), held -- the empty
  pair satisfies it. This variant composes farkas-vector-round-covered with the
  unit-column re-presentation, threading the covering through: the round gives
  affine lists with length(l)+length(u) = length(packed rows); repr preserves
  length (farkas-vector-unit-repr-length); so the re-presented next-variable
  lists satisfy length(repr l)+length(repr u) = length(packed rows). Hence the
  step's held-goal carries that covering and is NOT empty-satisfiable.

  Still DIRECTION-NEUTRAL: this fixes the step's existential vacuity; it does not
  touch the Feasible predicate whose uniformity in k is the Option 1/2 collapse
  (feasible-step / eliminate remain unmigrated). Built additively; the original
  farkas-vector-step is untouched. Depends on farkas-vector-round-covered, so it
  breaks loudly if that keystone chain stops holding. Native proof data,
  axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-vector-round-covered :as vrc]
            [rainbow.math.rational.nnrat.farkas-vector-unit-column :as vuc]
            [rainbow.math.rational.nnrat.farkas-vector-unit-repr-length :as rl]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))
(def p2 (product nnrat nnrat))
(def arow (product nnrat p2))
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def aff-pair (product list-a list-a))
(def nvc-pair (product list-nvc list-nvc))
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))
(def nat (function/const* 'data/Nat []))
(def one (function/const* 'nnrat/one []))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both] (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both] (function/app (function/const* 'proposition/right []) l r both))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- lowers-hold [cs x] (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold []) cs x))
(defn- uppers-hold [cs x] (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold []) cs x))
(defn- map-uppers [lst x] (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) lst x))
(defn- repr [rows] (function/app (function/const* 'nnrat/farkas-vector-unit-repr []) rows))
(defn- unit-lower [rows x2 h] (function/app (function/const* 'nnrat/farkas-vector-unit-column-lower []) rows x2 h))
(defn- unit-upper [rows x2 h] (function/app (function/const* 'nnrat/farkas-vector-unit-column-upper []) rows x2 h))
(defn- len-a [l] (function/app (function/const* 'list/length [type-level]) arow l))
(defn- len-nvc [l] (function/app (function/const* 'list/length [type-level]) nvc l))
(defn- len-bs [l] (function/app (function/const* 'list/length [type-level]) bs-row l))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- neq [a b] (function/equality type-level nat a b))
(defn- congr [f a b h]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat f a b h))
(defn- eq-trans [x y z hxy hyz]
  (function/app (function/const* 'equality/transitive [type-level]) nat x y z hxy hyz))
(defn- repr-length [rows]
  (function/app (function/const* 'nnrat/farkas-vector-unit-repr-length []) rows))
(defn- packed [descs] (function/app (function/const* 'nnrat/farkas-vector-partition-packed []) descs))
(defn- descs-bilist [lowers uppers]
  (function/app (function/const* 'nnrat/farkas-adapter-descs-bilist []) lowers uppers))
(defn- round-covered [lowers uppers x1 x2 lh uh]
  (function/app (function/const* 'nnrat/farkas-vector-round-covered []) lowers uppers x1 x2 lh uh))

(defn- exists [T pred] (function/app (function/const* 'proposition/existence [type-level]) T pred))
(defn- witness [T pred v ev] (function/app (function/const* 'proposition/witness [type-level]) T pred v ev))
(defn- use-witness [T pred result ev cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) T pred result ev cont))

;; rs = the packed rows of this round (covering RHS)
(defn- rs-of [lowers uppers] (packed (descs-bilist lowers uppers)))

;; the round's covered affine goal predicate (matches round-covered's goal)
(defn- aff-goal-pred [rs w]
  (function/lam
   [['pr aff-pair]]
   (conjunction (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                             (uppers-sat (snd list-a list-a 'pr) w))
                (neq (nadd (len-a (fst list-a list-a 'pr)) (len-a (snd list-a list-a 'pr)))
                     (len-bs rs)))))
;; the step's covered held goal predicate / goal
(defn- held-goal-pred [rs w]
  (function/lam
   [['pr nvc-pair]]
   (conjunction (conjunction (lowers-hold (map-uppers (fst list-nvc list-nvc 'pr) one) w)
                             (uppers-hold (map-uppers (snd list-nvc list-nvc 'pr) one) w))
                (neq (nadd (len-nvc (fst list-nvc list-nvc 'pr)) (len-nvc (snd list-nvc list-nvc 'pr)))
                     (len-bs rs)))))
(defn- held-goal [rs w] (exists nvc-pair (held-goal-pred rs w)))

(def step-covered-spec
  {:name 'nnrat/farkas-vector-step-covered
   :universes []
   :type
   (function/forall
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (held-goal (rs-of 'lowers 'uppers) 'x2))
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['lh (lowers-hold (map-uppers 'lowers 'x2) 'x1)]
     ['uh (uppers-hold (map-uppers 'uppers 'x2) 'x1)]]
    (let [rs (rs-of 'lowers 'uppers)
          round-out (round-covered 'lowers 'uppers 'x1 'x2 'lh 'uh)]
      (use-witness
       aff-pair (aff-goal-pred rs 'x2) (held-goal rs 'x2) round-out
       (function/lam
        [['pr aff-pair]
         ['pp (function/app (aff-goal-pred rs 'x2) 'pr)]]
        (let [l-aff (fst list-a list-a 'pr)
              u-aff (snd list-a list-a 'pr)
              sat-conj (conjunction (lowers-sat l-aff 'x2) (uppers-sat u-aff 'x2))
              lenq (neq (nadd (len-a l-aff) (len-a u-aff)) (len-bs rs))
              sat-conj0 (left-conjunct sat-conj lenq 'pp)
              len-eq0 (right-conjunct sat-conj lenq 'pp)
              lsat (left-conjunct (lowers-sat l-aff 'x2) (uppers-sat u-aff 'x2) sat-conj0)
              usat (right-conjunct (lowers-sat l-aff 'x2) (uppers-sat u-aff 'x2) sat-conj0)
              held-lo (unit-lower l-aff 'x2 lsat)
              held-up (unit-upper u-aff 'x2 usat)
              rl-l (repr-length l-aff) rl-u (repr-length u-aff)
              A (nadd (len-nvc (repr l-aff)) (len-nvc (repr u-aff)))
              B (nadd (len-a l-aff) (len-nvc (repr u-aff)))
              C (nadd (len-a l-aff) (len-a u-aff))
              D (len-bs rs)
              f-left (function/lam [['x nat]] (nadd 'x (len-nvc (repr u-aff))))
              f-right (function/lam [['x nat]] (nadd (len-a l-aff) 'x))
              step1 (congr f-left (len-nvc (repr l-aff)) (len-a l-aff) rl-l)   ; A=B
              step2 (congr f-right (len-nvc (repr u-aff)) (len-a u-aff) rl-u)  ; B=C
              held-len (eq-trans A C D (eq-trans A B C step1 step2) len-eq0)   ; A=D
              new-pr (pair2 list-nvc list-nvc (repr l-aff) (repr u-aff))]
          (witness nvc-pair (held-goal-pred rs 'x2) new-pr
                   (conjoin (conjunction (lowers-hold (map-uppers (repr l-aff) one) 'x2)
                                         (uppers-hold (map-uppers (repr u-aff) one) 'x2))
                            (neq (nadd (len-nvc (repr l-aff)) (len-nvc (repr u-aff))) (len-bs rs))
                            (conjoin (lowers-hold (map-uppers (repr l-aff) one) 'x2)
                                     (uppers-hold (map-uppers (repr u-aff) one) 'x2)
                                     held-lo held-up)
                            held-len)))))))})

(def definition-specs [])
(def theorem-specs [step-covered-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      vrc/extend-environment
      vuc/extend-environment
      rl/extend-environment
      (support/extend-with :nnrat-farkas-vector-step-covered
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
