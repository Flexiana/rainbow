(ns rainbow.math.rational.nnrat.farkas-bridge-list
  "Piece 1 of the n-variable capstone:
  the bridge-mapping -- map the structured bridge over a list of cross rows.

  Each structured cross row bundles the cross-product parameters
  (w_lo, a_hi, a_lo, b_hi) with the affine block structure
  (c_hi, d_hi, c_lo, d_lo) -- a Product of two 4-tuples. Given the cross
  condition holds at w for every row (nnrat/farkas-bridge-cross-holds), the
  corresponding both-sides row A*w+P<=B*w+Q holds for every row
  (nnrat/farkas-bridge-both-sides-hold), by mapping the single-row bridge
  (nnrat/farkas-cross-to-both-sides) over the list with List.rec. This is
  the whole structured cross system recognized as a both-sides system --
  the mapped form of the eliminate-round's `link`. Native proof data,
  axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-cross-bridge :as bridge]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def p2 (product nnrat nnrat))
(def p3 (product nnrat p2))
(def p4 (product nnrat p3))
(def row (product p4 p4))
(def list-row (function/app (function/const* 'data/List [type-level]) row))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))

(defn- base [r] (fst p4 p4 r))
(defn- block [r] (snd p4 p4 r))
;; base4 = (w_lo, (a_hi, (a_lo, b_hi)))
(defn- w-lo [r] (fst nnrat p3 (base r)))
(defn- a-hi [r] (fst nnrat p2 (snd nnrat p3 (base r))))
(defn- a-lo [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat p3 (base r)))))
(defn- b-hi [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat p3 (base r)))))
;; block4 = (c_hi, (d_hi, (c_lo, d_lo)))
(defn- c-hi [r] (fst nnrat p3 (block r)))
(defn- d-hi [r] (fst nnrat p2 (snd nnrat p3 (block r))))
(defn- c-lo [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat p3 (block r)))))
(defn- d-lo [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat p3 (block r)))))

(defn- cross-at [r w]
  (at-most
   (add (mul (w-lo r) (a-hi r))
        (mul (add (mul (c-hi r) w) (d-hi r)) (a-lo r)))
   (add (mul (b-hi r) (a-lo r))
        (mul (add (mul (c-lo r) w) (d-lo r)) (a-hi r)))))
(defn- both-sides-at [r w]
  (at-most
   (add (mul (mul (c-hi r) (a-lo r)) w)
        (add (mul (w-lo r) (a-hi r)) (mul (d-hi r) (a-lo r))))
   (add (mul (mul (c-lo r) (a-hi r)) w)
        (add (mul (b-hi r) (a-lo r)) (mul (d-lo r) (a-hi r))))))

(defn- cross-holds [rows w]
  (function/app (function/const* 'nnrat/farkas-bridge-cross-holds []) rows w))
(defn- both-sides-hold [rows w]
  (function/app (function/const* 'nnrat/farkas-bridge-both-sides-hold []) rows w))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- cross-to-both-sides [wlo ahi alo bhi chi dhi clo dlo w cross]
  (function/app (function/const* 'nnrat/farkas-cross-to-both-sides [])
                wlo ahi alo bhi chi dhi clo dlo w cross))

(defn- fold-spec [name at-fn]
  {:name name :kind :definition :universes []
   :type (function/arrow list-row nnrat 'Prop)
   :value
   (function/lam
    [['rows list-row] ['w nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     row
     (function/lam [['ignored list-row]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head row] ['tail list-row] ['ih 'Prop]]
      (proposition/conjunction (at-fn 'head 'w) 'ih))
     'rows))})

(def cross-holds-spec
  (fold-spec 'nnrat/farkas-bridge-cross-holds cross-at))
(def both-sides-hold-spec
  (fold-spec 'nnrat/farkas-bridge-both-sides-hold both-sides-at))

(def definition-specs [cross-holds-spec both-sides-hold-spec])

(def bridge-list-necessary-spec
  {:name 'nnrat/farkas-bridge-list-necessary
   :universes []
   :type
   (function/forall
    [['rows list-row] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (both-sides-hold 'rows 'w))
   :value
   (function/lam
    [['rows list-row] ['w nnrat]
     ['crosses (cross-holds 'rows 'w)]]
    (let [motive (function/lam
                  [['rs list-row]]
                  (function/arrow (cross-holds 'rs 'w)
                                  (both-sides-hold 'rs 'w)))
          nil-case
          (function/lam
           [['hnil (cross-holds
                    (function/app (function/const* 'data/nil [type-level]) row)
                    'w)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head row] ['tail list-row]
            ['ih (function/arrow (cross-holds 'tail 'w)
                                 (both-sides-hold 'tail 'w))]]
           (function/lam
            [['hcons (cross-holds
                      (function/app (function/const* 'data/cons [type-level])
                                    row 'head 'tail)
                      'w)]]
            (let [head-cross (cross-at 'head 'w)
                  tail-prop (cross-holds 'tail 'w)
                  head-proof (left-conjunct head-cross tail-prop 'hcons)
                  tail-proof (right-conjunct head-cross tail-prop 'hcons)
                  head-bridged
                  (cross-to-both-sides (w-lo 'head) (a-hi 'head) (a-lo 'head)
                                       (b-hi 'head) (c-hi 'head) (d-hi 'head)
                                       (c-lo 'head) (d-lo 'head) 'w head-proof)]
              (conjoin (both-sides-at 'head 'w)
                       (both-sides-hold 'tail 'w)
                       head-bridged
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        row motive nil-case cons-case 'rows)
       'crosses)))})

(def theorem-specs [bridge-list-necessary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-cross-bridge])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-bridge-list (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-bridge-list))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
