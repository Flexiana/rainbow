(ns rainbow.math.rational.nnrat.farkas-reduce-align
  "Piece (i) of the n-variable capstone:
  the data-representation alignment that lets the elimination round close on
  structured cross rows.

  The bridge-mapping (nnrat/farkas-bridge-list-necessary) proves the
  both-sides conditions hold as a fold over STRUCTURED cross rows (base4 x
  block4); the recursive reduction (nnrat/farkas-reduce-list-necessary)
  consumes a fold over 4-TUPLE both-sides rows. This aligns them:
  nnrat/farkas-structured-to-both-sides maps each structured row to its
  4-tuple (A=c_hi*a_lo, B=c_lo*a_hi, P=w_lo*a_hi+d_hi*a_lo,
  Q=b_hi*a_lo+d_lo*a_hi), and nnrat/farkas-reduce-align proves the
  bridge-mapping's fold implies the reduction's fold over the mapped list --
  the per-row predicates are definitionally equal (the map's projections
  reduce to the fields), so a List.rec carries each head proof directly.

  nnrat/farkas-eliminate-structured then chains bridge-mapping -> align ->
  reduction: given the cross condition holds at w for every structured row,
  the reduced affine-row system holds. This is one full elimination round on
  the structured representation, with the `link` fully discharged -- the
  closed step the variable-count induction folds. Native proof data,
  axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-bridge-list :as bridge-list]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def p2 (product nnrat nnrat))
(def p3 (product nnrat p2))
(def p4 (product nnrat p3))
(def structured (product p4 p4))
(def list-structured
  (function/app (function/const* 'data/List [type-level]) structured))
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))

(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- nil-of [carrier]
  (function/app (function/const* 'data/nil [type-level]) carrier))
(defn- cons-of [carrier head tail]
  (function/app (function/const* 'data/cons [type-level]) carrier head tail))

;; structured-row field extractors (base4 = (w_lo,(a_hi,(a_lo,b_hi))),
;; block4 = (c_hi,(d_hi,(c_lo,d_lo))))
(defn- base [r] (fst p4 p4 r))
(defn- block [r] (snd p4 p4 r))
(defn- w-lo [r] (fst nnrat p3 (base r)))
(defn- a-hi [r] (fst nnrat p2 (snd nnrat p3 (base r))))
(defn- a-lo [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat p3 (base r)))))
(defn- b-hi [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat p3 (base r)))))
(defn- c-hi [r] (fst nnrat p3 (block r)))
(defn- d-hi [r] (fst nnrat p2 (snd nnrat p3 (block r))))
(defn- c-lo [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat p3 (block r)))))
(defn- d-lo [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat p3 (block r)))))

;; the 4-tuple both-sides row (A,(B,(P,Q))) derived from a structured row
(defn- mk-bs [r]
  (let [ar (mul (c-hi r) (a-lo r))
        br (mul (c-lo r) (a-hi r))
        pr (add (mul (w-lo r) (a-hi r)) (mul (d-hi r) (a-lo r)))
        qr (add (mul (b-hi r) (a-lo r)) (mul (d-lo r) (a-hi r)))]
    (pair nnrat bpq ar (pair nnrat p2 br (pair nnrat nnrat pr qr)))))

(defn- both-sides-hold [rows w]
  (function/app (function/const* 'nnrat/farkas-bridge-both-sides-hold []) rows w))
(defn- cross-holds [rows w]
  (function/app (function/const* 'nnrat/farkas-bridge-cross-holds []) rows w))
(defn- both-sides-at [r w]
  (function/app (function/const* 'nnrat/farkas-bridge-both-sides-hold [])
                (cons-of structured r (nil-of structured)) w))
(defn- bs-satisfied [rows w]
  (function/app (function/const* 'nnrat/farkas-both-sides-rows-satisfied []) rows w))
(defn- reduced-conditions [rows w]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows w))
(defn- to-bs [rows]
  (function/app (function/const* 'nnrat/farkas-structured-to-both-sides []) rows))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))

;; the per-row both-sides predicates, replicated so the folds line up
(defn- bh-at [r w]
  (function/app (function/const* 'nnrat/at-most [])
                (add (mul (mul (c-hi r) (a-lo r)) w)
                     (add (mul (w-lo r) (a-hi r)) (mul (d-hi r) (a-lo r))))
                (add (mul (mul (c-lo r) (a-hi r)) w)
                     (add (mul (b-hi r) (a-lo r)) (mul (d-lo r) (a-hi r))))))

;; map: structured rows -> 4-tuple both-sides rows
(def to-bs-spec
  {:name 'nnrat/farkas-structured-to-both-sides
   :kind :definition
   :universes []
   :type (function/arrow list-structured list-bs)
   :value
   (function/lam
    [['rows list-structured]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     structured
     (function/lam [['ignored list-structured]] list-bs)
     (nil-of bs-row)
     (function/lam
      [['head structured] ['tail list-structured] ['ih list-bs]]
      (cons-of bs-row (mk-bs 'head) 'ih))
     'rows))})

(def definition-specs [to-bs-spec])

;; align: the bridge-mapping's fold implies the reduction's fold over the map
(def align-spec
  {:name 'nnrat/farkas-reduce-align
   :universes []
   :type
   (function/forall
    [['rows list-structured] ['w nnrat]
     ['hold (both-sides-hold 'rows 'w)]]
    (bs-satisfied (to-bs 'rows) 'w))
   :value
   (function/lam
    [['rows list-structured] ['w nnrat]
     ['hold (both-sides-hold 'rows 'w)]]
    (let [motive (function/lam
                  [['rs list-structured]]
                  (function/arrow (both-sides-hold 'rs 'w)
                                  (bs-satisfied (to-bs 'rs) 'w)))
          nil-case
          (function/lam
           [['hnil (both-sides-hold (nil-of structured) 'w)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head structured] ['tail list-structured]
            ['ih (function/arrow (both-sides-hold 'tail 'w)
                                 (bs-satisfied (to-bs 'tail) 'w))]]
           (function/lam
            [['hcons (both-sides-hold
                      (cons-of structured 'head 'tail) 'w)]]
            (let [head-prop (bh-at 'head 'w)
                  tail-prop (both-sides-hold 'tail 'w)
                  head-proof (left-conjunct head-prop tail-prop 'hcons)
                  tail-proof (right-conjunct head-prop tail-prop 'hcons)]
              ;; row-both-sides(mk-bs head) w is defeq bh-at head w, so
              ;; head-proof types at both; conjoin into the mapped fold.
              (conjoin head-prop
                       (bs-satisfied (to-bs 'tail) 'w)
                       head-proof
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        structured motive nil-case cons-case 'rows)
       'hold)))})

;; the full elimination round on structured rows: cross holds -> reduced system
(def eliminate-structured-spec
  {:name 'nnrat/farkas-eliminate-structured
   :universes []
   :type
   (function/forall
    [['rows list-structured] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (reduced-conditions (to-bs 'rows) 'w))
   :value
   (function/lam
    [['rows list-structured] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (function/app
     (function/const* 'nnrat/farkas-reduce-list-necessary [])
     (to-bs 'rows) 'w
     (function/app
      (function/const* 'nnrat/farkas-reduce-align [])
      'rows 'w
      (function/app
       (function/const* 'nnrat/farkas-bridge-list-necessary [])
       'rows 'w 'crosses))))})

(def theorem-specs [align-spec eliminate-structured-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-bridge-list rainbow.math.rational.nnrat.farkas-reduce-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-reduce-align (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-reduce-align))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
