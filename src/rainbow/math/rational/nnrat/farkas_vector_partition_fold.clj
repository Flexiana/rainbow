(ns rainbow.math.rational.nnrat.farkas-vector-partition-fold
  "The unified representation, partition bridge (the fold)
 : collect a LIST of reduced
  coefficient-vector rows into the affine partition's input.

  The 2026-09-09 finding: farkas-partition-list-necessary is generic in the
  per-row (A,B,P,Q), so the coefficient-vector round bridges to it rather
  than re-proving a partition. nnrat/farkas-vector-partition-pack packed one
  reduced row; this folds that across the round's reduced rows.

  A reduced (lower,upper) pair is a descriptor bundling
  (l1, u1, b_L, b_U, a2l, a2u, rl, ru): the two x1-coefficients, the two
  bounds, and -- with the next variable x2 the head of each tail -- the two
  x2-coefficients and the two rest-vectors. nnrat/farkas-vector-partition-fold
  takes a list of these and a proof that each one's reduced both-sides vector
  row holds at x2 (all-input-rows, a conjunction fold), and produces
  farkas-reduced-conditions of the packed both-sides DATA list
  (packed-list = the per-descriptor packed rows). Proof: List.rec over the
  descriptors; nil is truth, each cons discharges its head via
  nnrat/farkas-vector-both-sides-reduce (defeq to reduce-list's row-reduced
  of the packed row) conjoined with the tail's fold. The packed list and this
  proof are exactly farkas-partition-list-necessary's two inputs, so feeding
  them yields the next round's affine lower/upper lists -- the round's
  reduction to a system in one fewer variable, on the coefficient-vector
  representation. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce :as vbsr]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; descriptor: (l1,(u1,(bL,(bU,(a2l,(a2u,(rl,ru)))))))
(def t1 (product lp lp))
(def t2 (product nnrat t1))
(def t3 (product nnrat t2))
(def t4 (product nnrat t3))
(def t5 (product nnrat t4))
(def t6 (product nnrat t5))
(def desc (product nnrat t6))
(def list-desc (function/app (function/const* 'data/List [type-level]) desc))

;; reduce-list's both-sides row shape (A,(B,(P,Q))) and its list
(def pq pair-nn)
(def bpq (product nnrat pq))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- pnn [x y] (pair2 nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- cons-bs [h t] (function/app (function/const* 'data/cons [type-level]) bs-row h t))
(def nil-bs (function/app (function/const* 'data/nil [type-level]) bs-row))
(defn- cons-desc [h t] (function/app (function/const* 'data/cons [type-level]) desc h t))
(def nil-desc (function/app (function/const* 'data/nil [type-level]) desc))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- disjunction [l r] (function/app (function/const* 'proposition/disjunction []) l r))
(defn- existence [pred]
  (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- reduced-conditions [rows v]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows v))
(defn- vec-reduce [lc uc bl bu a2l a2u rl ru x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-both-sides-reduce [])
                lc uc bl bu a2l a2u rl ru x2 h))

;; descriptor field extractors (on a descriptor term d)
(defn- d-lc [d] (fst nnrat t6 d))
(defn- d-r6 [d] (snd nnrat t6 d))
(defn- d-uc [d] (fst nnrat t5 (d-r6 d)))
(defn- d-r5 [d] (snd nnrat t5 (d-r6 d)))
(defn- d-bl [d] (fst nnrat t4 (d-r5 d)))
(defn- d-r4 [d] (snd nnrat t4 (d-r5 d)))
(defn- d-bu [d] (fst nnrat t3 (d-r4 d)))
(defn- d-r3 [d] (snd nnrat t3 (d-r4 d)))
(defn- d-a2l [d] (fst nnrat t2 (d-r3 d)))
(defn- d-r2 [d] (snd nnrat t2 (d-r3 d)))
(defn- d-a2u [d] (fst nnrat t1 (d-r2 d)))
(defn- d-r1 [d] (snd nnrat t1 (d-r2 d)))
(defn- d-rl [d] (fst lp lp (d-r1 d)))
(defn- d-ru [d] (snd lp lp (d-r1 d)))

;; per-descriptor derived quantities
(defn- d-al [d] (mul (d-a2u d) (d-lc d)))
(defn- d-ar [d] (mul (d-a2l d) (d-uc d)))
(defn- d-pp [d] (add (mul (d-bl d) (d-uc d)) (eval-form (scale-right (d-lc d) (d-ru d)))))
(defn- d-qq [d] (add (mul (d-bu d) (d-lc d)) (eval-form (scale-right (d-uc d) (d-rl d)))))

;; the reduced both-sides vector row for descriptor d at x2 (vec-reduce input)
(defn- input-row [d x2]
  (at-most (add (mul (d-bl d) (d-uc d))
                (eval-form (scale-right (d-lc d) (cons-pair (pnn (d-a2u d) x2) (d-ru d)))))
           (add (mul (d-bu d) (d-lc d))
                (eval-form (scale-right (d-uc d) (cons-pair (pnn (d-a2l d) x2) (d-rl d)))))))

;; the packed both-sides data row for descriptor d
(defn- pack-data [d]
  (pair2 nnrat bpq (d-al d)
         (pair2 nnrat pq (d-ar d) (pnn (d-pp d) (d-qq d)))))

;; row-reduced (pack-data d) x2, spelled out (defeq to vec-reduce's output)
(defn- row-reduced [d x2]
  (disjunction
   (existence (function/lam [['dd nnrat]]
                            (conjunction (equiv (add (d-al d) 'dd) (d-ar d))
                                         (at-most (d-pp d) (add (mul 'dd x2) (d-qq d))))))
   (existence (function/lam [['dd nnrat]]
                            (conjunction (equiv (add (d-ar d) 'dd) (d-al d))
                                         (at-most (add (mul 'dd x2) (d-pp d)) (d-qq d)))))))

;; all-input-rows descs x2 : each descriptor's reduced row holds (conj fold)
(def all-input-rows-spec
  {:name 'nnrat/farkas-vector-partition-input-rows
   :kind :definition
   :universes []
   :type (function/arrow list-desc nnrat 'Prop)
   :value
   (function/lam
    [['descs list-desc] ['x2 nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     desc
     (function/lam [['ignored list-desc]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head desc] ['tail list-desc] ['ih 'Prop]]
      (proposition/conjunction (input-row 'head 'x2) 'ih))
     'descs))})

;; packed-list descs : the per-descriptor packed both-sides rows
(def packed-list-spec
  {:name 'nnrat/farkas-vector-partition-packed
   :kind :definition
   :universes []
   :type (function/arrow list-desc list-bs)
   :value
   (function/lam
    [['descs list-desc]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     desc
     (function/lam [['ignored list-desc]] list-bs)
     nil-bs
     (function/lam
      [['head desc] ['tail list-desc] ['ih list-bs]]
      (cons-bs (pack-data 'head) 'ih))
     'descs))})

(def definition-specs [all-input-rows-spec packed-list-spec])

(defn- all-input-rows [descs x2]
  (function/app (function/const* 'nnrat/farkas-vector-partition-input-rows [])
                descs x2))
(defn- packed-list [descs]
  (function/app (function/const* 'nnrat/farkas-vector-partition-packed []) descs))

(def partition-fold-spec
  {:name 'nnrat/farkas-vector-partition-fold
   :universes []
   :type
   (function/forall
    [['descs list-desc] ['x2 nnrat] ['h (all-input-rows 'descs 'x2)]]
    (reduced-conditions (packed-list 'descs) 'x2))
   :value
   (function/lam
    [['descs list-desc] ['x2 nnrat] ['h (all-input-rows 'descs 'x2)]]
    (let [motive (function/lam
                  [['ds list-desc]]
                  (function/arrow (all-input-rows 'ds 'x2)
                                  (reduced-conditions (packed-list 'ds) 'x2)))
          nil-case
          (function/lam
           [['hnil (all-input-rows nil-desc 'x2)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head desc] ['tail list-desc]
            ['ih (function/arrow (all-input-rows 'tail 'x2)
                                 (reduced-conditions (packed-list 'tail) 'x2))]]
           (function/lam
            [['hcons (all-input-rows (cons-desc 'head 'tail) 'x2)]]
            (let [head-prop (input-row 'head 'x2)
                  tail-prop (all-input-rows 'tail 'x2)
                  head-proof (left-conjunct head-prop tail-prop 'hcons)
                  tail-proof (right-conjunct head-prop tail-prop 'hcons)]
              (conjoin (row-reduced 'head 'x2)
                       (reduced-conditions (packed-list 'tail) 'x2)
                       (vec-reduce (d-lc 'head) (d-uc 'head) (d-bl 'head) (d-bu 'head)
                                   (d-a2l 'head) (d-a2u 'head) (d-rl 'head) (d-ru 'head)
                                   'x2 head-proof)
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        desc motive nil-case cons-case 'descs)
       'h)))})

(def theorem-specs [partition-fold-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-both-sides-reduce rainbow.math.rational.nnrat.farkas-reduce-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-partition-fold (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-partition-fold))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
