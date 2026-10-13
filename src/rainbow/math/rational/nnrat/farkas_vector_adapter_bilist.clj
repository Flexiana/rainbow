(ns rainbow.math.rational.nnrat.farkas-vector-adapter-bilist
  "The unified representation, partition bridge adapter (the bilist)
 : turn one whole elimination round's
  reduced conditions into the flat descriptor fold the bridge consumes.

  farkas-cross-vectors-all-reduced-conds is the round's reduced conditions: a
  conjunction fold over the LOWER list, each entry the per-lower
  farkas-cross-vectors-reduced fold over the upper list. The per-upper adapter
  (nnrat/farkas-vector-adapter-list) already turns one lower's entry into the
  flat all-input-rows fold over that lower's descriptor list. This folds that
  over the lower list.

  Representing lowers and uppers as next-variable constraints
  (coeff,(bound,(a2,rest))) and mapping them to the round's list form at x2
  (farkas-adapter-map-uppers), the round's all-reduced conditions imply
  all-input-rows of the concatenated per-lower descriptor lists
  (nnrat/farkas-adapter-descs-bilist = append the per-lower descriptor lists).
  Proof: List.rec over the lowers; each cons applies the per-upper adapter to
  its head entry and the induction hypothesis to the tail, then joins them
  with the append lemma nnrat/farkas-vector-input-rows-append
  (all-input-rows distributes over list/append). The concatenated descriptor
  list and this proof are exactly the bridge fold's input
  (farkas-vector-partition-fold), whose output is
  farkas-partition-list-necessary's input -- so composing adapter + fold +
  partition gives one closed coefficient-vector round: a feasible system in
  k+1 variables yields a feasible system in k. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-list :as val]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-bilist :as cvb]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; next-variable constraint (coeff,(bound,(a2,rest))) and its list
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))

;; bridge descriptor (matches vpf / adapter-list nesting)
(def t1 (product lp lp))
(def t2 (product nnrat t1))
(def t3 (product nnrat t2))
(def t4 (product nnrat t3))
(def t5 (product nnrat t4))
(def t6 (product nnrat t5))
(def desc (product nnrat t6))
(def list-desc (function/app (function/const* 'data/List [type-level]) desc))

;; cross-vectors constraint = (coeff,(tail,bound)); the round's list form
(def tb (product lp nnrat))
(def uc (product nnrat tb))
(def list-c (function/app (function/const* 'data/List [type-level]) uc))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pnn [x y] (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- cons-desc [h t] (function/app (function/const* 'data/cons [type-level]) desc h t))
(def nil-desc (function/app (function/const* 'data/nil [type-level]) desc))
(defn- cons-nvc [h t] (function/app (function/const* 'data/cons [type-level]) nvc h t))
(def nil-nvc (function/app (function/const* 'data/nil [type-level]) nvc))
(defn- append-desc [xs ys]
  (function/app (function/const* 'list/append [type-level]) desc xs ys))

;; nvc field extractors
(defn- n-coeff [u] (fst nnrat n-br u))
(defn- n-bound [u] (fst nnrat n-ar (snd nnrat n-br u)))
(defn- n-a2 [u] (fst nnrat lp (snd nnrat n-ar (snd nnrat n-br u))))
(defn- n-rest [u] (snd nnrat lp (snd nnrat n-ar (snd nnrat n-br u))))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))

;; descriptor projections (match vpf's d-* exactly)
(defn- d-lc [d] (fst nnrat t6 d))
(defn- d-uc [d] (fst nnrat t5 (snd nnrat t6 d)))
(defn- d-bl [d] (fst nnrat t4 (snd nnrat t5 (snd nnrat t6 d))))
(defn- d-bu [d] (fst nnrat t3 (snd nnrat t4 (snd nnrat t5 (snd nnrat t6 d)))))
(defn- d-a2l [d] (fst nnrat t2 (snd nnrat t3 (snd nnrat t4 (snd nnrat t5 (snd nnrat t6 d))))))
(defn- d-a2u [d] (fst nnrat t1 (snd nnrat t2 (snd nnrat t3 (snd nnrat t4 (snd nnrat t5 (snd nnrat t6 d)))))))
(defn- d-rl [d] (fst lp lp (snd nnrat t1 (snd nnrat t2 (snd nnrat t3 (snd nnrat t4 (snd nnrat t5 (snd nnrat t6 d))))))))
(defn- d-ru [d] (snd lp lp (snd nnrat t1 (snd nnrat t2 (snd nnrat t3 (snd nnrat t4 (snd nnrat t5 (snd nnrat t6 d))))))))

(defn- all-input-rows [descs x2]
  (function/app (function/const* 'nnrat/farkas-vector-partition-input-rows []) descs x2))
;; vpf's per-descriptor reduced row (for naming conjuncts in the append lemma)
(defn- input-row-of [d x2]
  (at-most (add (mul (d-bl d) (d-uc d))
                (eval-form (scale-right (d-lc d) (cons-pair (pnn (d-a2u d) x2) (d-ru d)))))
           (add (mul (d-bu d) (d-lc d))
                (eval-form (scale-right (d-uc d) (cons-pair (pnn (d-a2l d) x2) (d-rl d)))))))
(defn- map-uppers [uppers x2]
  (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) uppers x2))
(defn- descs-of-lower [l-coeff b-l a2l rl uppers]
  (function/app (function/const* 'nnrat/farkas-adapter-descs-of-lower [])
                l-coeff b-l a2l rl uppers))
(defn- adapter-list [l-coeff b-l a2l rl uppers x1 x2 h]
  (function/app (function/const* 'nnrat/farkas-vector-adapter-list [])
                l-coeff b-l a2l rl uppers x1 x2 h))
(defn- all-reduced-conds [lowers uppers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-all-reduced-conds [])
                lowers uppers x1))
(defn- reduced-conds [uppers x1 l-coeff l-tail b-l]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced [])
                uppers x1 l-coeff l-tail b-l))

;; ------ all-input-rows distributes over list/append ------
(def input-rows-append-spec
  {:name 'nnrat/farkas-vector-input-rows-append
   :universes []
   :type
   (function/forall
    [['xs list-desc] ['ys list-desc] ['x2 nnrat]
     ['hx (all-input-rows 'xs 'x2)] ['hy (all-input-rows 'ys 'x2)]]
    (all-input-rows (append-desc 'xs 'ys) 'x2))
   :value
   (function/lam
    [['xs list-desc] ['ys list-desc] ['x2 nnrat]
     ['hx (all-input-rows 'xs 'x2)] ['hy (all-input-rows 'ys 'x2)]]
    (let [motive (function/lam
                  [['zs list-desc]]
                  (function/arrow (all-input-rows 'zs 'x2)
                                  (all-input-rows (append-desc 'zs 'ys) 'x2)))
          nil-case
          (function/lam [['hnil (all-input-rows nil-desc 'x2)]] 'hy)
          cons-case
          (function/lam
           [['head desc] ['tail list-desc]
            ['ih (function/arrow (all-input-rows 'tail 'x2)
                                 (all-input-rows (append-desc 'tail 'ys) 'x2))]]
           (function/lam
            [['hcons (all-input-rows (cons-desc 'head 'tail) 'x2)]]
            (let [hp (input-row-of 'head 'x2)
                  tp (all-input-rows 'tail 'x2)
                  head-proof (left-conjunct hp tp 'hcons)
                  tail-proof (right-conjunct hp tp 'hcons)]
              (conjoin hp (all-input-rows (append-desc 'tail 'ys) 'x2)
                       head-proof (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        desc motive nil-case cons-case 'xs)
       'hx)))})

(def definition-specs [])

;; ------ concatenated per-lower descriptor lists ------
(def descs-bilist-spec
  {:name 'nnrat/farkas-adapter-descs-bilist
   :kind :definition
   :universes []
   :type (function/arrow list-nvc list-nvc list-desc)
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nvc
     (function/lam [['ignored list-nvc]] list-desc)
     nil-desc
     (function/lam
      [['head nvc] ['tail list-nvc] ['ih list-desc]]
      (append-desc (descs-of-lower (n-coeff 'head) (n-bound 'head)
                                   (n-a2 'head) (n-rest 'head) 'uppers)
                   'ih))
     'lowers))})

(def definition-specs-2 [descs-bilist-spec])

(defn- descs-bilist [lowers uppers]
  (function/app (function/const* 'nnrat/farkas-adapter-descs-bilist []) lowers uppers))
(defn- input-rows-append [xs ys x2 hx hy]
  (function/app (function/const* 'nnrat/farkas-vector-input-rows-append [])
                xs ys x2 hx hy))

;; ------ the bilist adapter ------
(def adapter-bilist-spec
  {:name 'nnrat/farkas-vector-adapter-bilist
   :universes []
   :type
   (function/forall
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['h (all-reduced-conds (map-uppers 'lowers 'x2) (map-uppers 'uppers 'x2) 'x1)]]
    (all-input-rows (descs-bilist 'lowers 'uppers) 'x2))
   :value
   (function/lam
    [['lowers list-nvc] ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['h (all-reduced-conds (map-uppers 'lowers 'x2) (map-uppers 'uppers 'x2) 'x1)]]
    (let [mapU (map-uppers 'uppers 'x2)
          motive (function/lam
                  [['ls list-nvc]]
                  (function/arrow
                   (all-reduced-conds (map-uppers 'ls 'x2) mapU 'x1)
                   (all-input-rows (descs-bilist 'ls 'uppers) 'x2)))
          nil-case
          (function/lam
           [['hnil (all-reduced-conds (map-uppers nil-nvc 'x2) mapU 'x1)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head nvc] ['tail list-nvc]
            ['ih (function/arrow
                  (all-reduced-conds (map-uppers 'tail 'x2) mapU 'x1)
                  (all-input-rows (descs-bilist 'tail 'uppers) 'x2))]]
           (function/lam
            [['hcons (all-reduced-conds (map-uppers (cons-nvc 'head 'tail) 'x2) mapU 'x1)]]
            (let [l-tail (cons-pair (pnn (n-a2 'head) 'x2) (n-rest 'head))
                  head-red (reduced-conds mapU 'x1 (n-coeff 'head) l-tail (n-bound 'head))
                  tail-red (all-reduced-conds (map-uppers 'tail 'x2) mapU 'x1)
                  head-proof (left-conjunct head-red tail-red 'hcons)
                  tail-proof (right-conjunct head-red tail-red 'hcons)
                  head-rows (adapter-list (n-coeff 'head) (n-bound 'head)
                                          (n-a2 'head) (n-rest 'head)
                                          'uppers 'x1 'x2 head-proof)
                  tail-rows (function/app 'ih tail-proof)]
              (input-rows-append
               (descs-of-lower (n-coeff 'head) (n-bound 'head)
                               (n-a2 'head) (n-rest 'head) 'uppers)
               (descs-bilist 'tail 'uppers)
               'x2 head-rows tail-rows))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        nvc motive nil-case cons-case 'lowers)
       'h)))})

(def theorem-specs [input-rows-append-spec adapter-bilist-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-vector-adapter-list rainbow.math.rational.nnrat.farkas-cross-vectors-bilist])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-vector-adapter-bilist (concat definition-specs [input-rows-append-spec] definition-specs-2 [adapter-bilist-spec]))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-vector-adapter-bilist))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs-2))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment [input-rows-append-spec adapter-bilist-spec]))
