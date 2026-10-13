(ns rainbow.math.rational.nnrat.farkas-vector-adapter-list
  "The unified representation, partition bridge adapter (per-upper list)
 : turn one round's per-lower reduced
  conditions into the flat descriptor fold the bridge consumes.

  farkas-cross-vectors-reduced (brick 3's one-lower fold) proves, for one
  lower row against a list of upper rows, that every pairwise reduced
  both-sides vector condition (reduced-at) holds -- a NESTED conjunction fold
  in the coefficient-vector (list-u) representation. The bridge fold
  (farkas-vector-partition-fold) instead wants a FLAT all-input-rows fold
  over descriptors (l1,u1,bL,bU,a2l,a2u,rl,ru). The two are the same
  proposition once each upper carries its next-variable coefficient
  explicitly: a next-variable constraint is (coeff,(bound,(a2,rest))), whose
  cross-vectors tail is cons((a2,x2),rest); for such an upper,
  reduced-at(map-to-c upper) is DEFINITIONALLY input-row(descriptor(lower,
  upper)) at x2 (same coefficients, same scaled tails).

  nnrat/farkas-vector-adapter-list is the List.rec transporting the nested
  fold to the flat one, conjunct by conjunct via that defeq: given
  farkas-cross-vectors-reduced holds for the mapped upper list, all-input-rows
  holds for the per-upper descriptor list (nnrat/farkas-adapter-descs-of-lower
  = map (upper -> descriptor(lower,upper))). Folding this over the lower list
  next gives the whole round's descriptor list, which the bridge fold + the
  already-proved partition turn into the next round's affine system. Native
  proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-partition-fold :as vpf]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-list :as cvl]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; next-variable constraint: (coeff,(bound,(a2,rest)))
(def n-ar (product nnrat lp))       ; (a2, rest)
(def n-br (product nnrat n-ar))     ; (bound, (a2,rest))
(def nvc (product nnrat n-br))      ; (coeff, (bound,(a2,rest)))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))

;; cross-vectors-list's upper constraint: (coeff,(tail,bound))
(def tb (product lp nnrat))
(def uc (product nnrat tb))
(def list-u (function/app (function/const* 'data/List [type-level]) uc))

;; the bridge descriptor (must match vpf's nesting exactly)
(def t1 (product lp lp))
(def t2 (product nnrat t1))
(def t3 (product nnrat t2))
(def t4 (product nnrat t3))
(def t5 (product nnrat t4))
(def t6 (product nnrat t5))
(def desc (product nnrat t6))
(def list-desc (function/app (function/const* 'data/List [type-level]) desc))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- pnn [x y] (pair2 nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- cons-u [h t] (function/app (function/const* 'data/cons [type-level]) uc h t))
(def nil-u (function/app (function/const* 'data/nil [type-level]) uc))
(def nil-nvc (function/app (function/const* 'data/nil [type-level]) nvc))
(defn- cons-nvc [h t] (function/app (function/const* 'data/cons [type-level]) nvc h t))
(defn- cons-desc [h t] (function/app (function/const* 'data/cons [type-level]) desc h t))
(def nil-desc (function/app (function/const* 'data/nil [type-level]) desc))

;; nvc field extractors
(defn- n-coeff [u] (fst nnrat n-br u))
(defn- n-br-of [u] (snd nnrat n-br u))
(defn- n-bound [u] (fst nnrat n-ar (n-br-of u)))
(defn- n-ar-of [u] (snd nnrat n-ar (n-br-of u)))
(defn- n-a2 [u] (fst nnrat lp (n-ar-of u)))
(defn- n-rest [u] (snd nnrat lp (n-ar-of u)))

;; map a next-variable upper to a cross-vectors-list upper at x2
(defn- map-c [u x2]
  (pair2 nnrat tb (n-coeff u)
         (pair2 lp nnrat (cons-pair (pnn (n-a2 u) x2) (n-rest u)) (n-bound u))))

;; descriptor for (lower fields, upper nvc)
(defn- desc-of [l-coeff b-l a2l rl u]
  (pair2 nnrat t6 l-coeff
         (pair2 nnrat t5 (n-coeff u)
                (pair2 nnrat t4 b-l
                       (pair2 nnrat t3 (n-bound u)
                              (pair2 nnrat t2 a2l
                                     (pair2 nnrat t1 (n-a2 u)
                                            (pair2 lp lp rl (n-rest u)))))))))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- reduced-conds [uppers x1 l-coeff l-tail b-l]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced [])
                uppers x1 l-coeff l-tail b-l))
(defn- all-input-rows [descs x2]
  (function/app (function/const* 'nnrat/farkas-vector-partition-input-rows [])
                descs x2))

;; map-c over a list of next-variable uppers
(def map-c-list-spec
  {:name 'nnrat/farkas-adapter-map-uppers
   :kind :definition
   :universes []
   :type (function/arrow list-nvc nnrat list-u)
   :value
   (function/lam
    [['uppers list-nvc] ['x2 nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nvc
     (function/lam [['ignored list-nvc]] list-u)
     nil-u
     (function/lam
      [['head nvc] ['tail list-nvc] ['ih list-u]]
      (cons-u (map-c 'head 'x2) 'ih))
     'uppers))})

;; the per-upper descriptor list for one lower
(def descs-of-lower-spec
  {:name 'nnrat/farkas-adapter-descs-of-lower
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nnrat lp list-nvc list-desc)
   :value
   (function/lam
    [['l-coeff nnrat] ['b-l nnrat] ['a2l nnrat] ['rl lp] ['uppers list-nvc]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nvc
     (function/lam [['ignored list-nvc]] list-desc)
     nil-desc
     (function/lam
      [['head nvc] ['tail list-nvc] ['ih list-desc]]
      (cons-desc (desc-of 'l-coeff 'b-l 'a2l 'rl 'head) 'ih))
     'uppers))})

(def definition-specs [map-c-list-spec descs-of-lower-spec])

(defn- map-c-list [uppers x2]
  (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) uppers x2))
(defn- descs-of-lower [l-coeff b-l a2l rl uppers]
  (function/app (function/const* 'nnrat/farkas-adapter-descs-of-lower [])
                l-coeff b-l a2l rl uppers))

;; a single reduced-at conjunct (cross-vectors-list's per-upper condition),
;; needed to name the conjuncts split from the hypothesis.
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
;; the per-upper reduced condition for (map-c u x2); x1 (the eliminated
;; variable) does not appear -- the tail head variable is x2, as map-c builds.
(defn- reduced-at [u x2 l-coeff l-tail b-l]
  (at-most (add (mul b-l (n-coeff u)) (eval-form (scale-right l-coeff (cons-pair (pnn (n-a2 u) x2) (n-rest u)))))
           (add (mul (n-bound u) l-coeff) (eval-form (scale-right (n-coeff u) l-tail)))))

(def adapter-list-spec
  {:name 'nnrat/farkas-vector-adapter-list
   :universes []
   :type
   (function/forall
    [['l-coeff nnrat] ['b-l nnrat] ['a2l nnrat] ['rl lp]
     ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['h (reduced-conds (map-c-list 'uppers 'x2) 'x1 'l-coeff
                        (cons-pair (pnn 'a2l 'x2) 'rl) 'b-l)]]
    (all-input-rows (descs-of-lower 'l-coeff 'b-l 'a2l 'rl 'uppers) 'x2))
   :value
   (function/lam
    [['l-coeff nnrat] ['b-l nnrat] ['a2l nnrat] ['rl lp]
     ['uppers list-nvc] ['x1 nnrat] ['x2 nnrat]
     ['h (reduced-conds (map-c-list 'uppers 'x2) 'x1 'l-coeff
                        (cons-pair (pnn 'a2l 'x2) 'rl) 'b-l)]]
    (let [l-tail (cons-pair (pnn 'a2l 'x2) 'rl)
          motive (function/lam
                  [['us list-nvc]]
                  (function/arrow
                   (reduced-conds (map-c-list 'us 'x2) 'x1 'l-coeff l-tail 'b-l)
                   (all-input-rows (descs-of-lower 'l-coeff 'b-l 'a2l 'rl 'us) 'x2)))
          nil-case
          (function/lam
           [['hnil (reduced-conds (map-c-list nil-nvc 'x2) 'x1 'l-coeff l-tail 'b-l)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head nvc] ['tail list-nvc]
            ['ih (function/arrow
                  (reduced-conds (map-c-list 'tail 'x2) 'x1 'l-coeff l-tail 'b-l)
                  (all-input-rows (descs-of-lower 'l-coeff 'b-l 'a2l 'rl 'tail) 'x2))]]
           (function/lam
            [['hcons (reduced-conds (map-c-list (cons-nvc 'head 'tail) 'x2) 'x1 'l-coeff l-tail 'b-l)]]
            ;; reduced-conds (cons (map-c head) ...) reduces to
            ;;   conjunction (reduced-at (map-c head) ...) (reduced-conds tail ...);
            ;; the head conjunct IS input-row(desc-of L head) x2 by defeq.
            (let [head-red (reduced-at 'head 'x2 'l-coeff l-tail 'b-l)
                  tail-red (reduced-conds (map-c-list 'tail 'x2) 'x1 'l-coeff l-tail 'b-l)
                  head-proof (left-conjunct head-red tail-red 'hcons)
                  tail-proof (right-conjunct head-red tail-red 'hcons)]
              (conjoin
               head-red
               (all-input-rows (descs-of-lower 'l-coeff 'b-l 'a2l 'rl 'tail) 'x2)
               head-proof
               (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        nvc motive nil-case cons-case 'uppers)
       'h)))})

(def theorem-specs [adapter-list-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      vpf/extend-environment
      cvl/extend-environment
      (support/extend-with :nnrat-farkas-vector-adapter-list
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
