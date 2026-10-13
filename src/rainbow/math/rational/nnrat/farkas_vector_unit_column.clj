(ns rainbow.math.rational.nnrat.farkas-vector-unit-column
  "The unified representation, unit-column re-presentation
 : re-present a round's affine output
  rows as next-variable coefficient constraints, so the round's output feeds
  its own input and successive rounds chain.

  nnrat/farkas-vector-round outputs affine rows in the just-partitioned
  variable x2: a lower row (a,(s,w)) satisfied at x2 means w <= a*x2 + s, an
  upper row (a,(s,b)) means a*x2 + s <= b (the constant s already folds in the
  remaining variables at the witness). The next round consumes next-variable
  constraints (coeff,(bound,(a2,rest))) whose hold-at form is
  bound <= eval(cons(coeff,x2) tail) (lower) / eval(...) <= bound (upper).
  The bridge is a UNIT COLUMN: carry the constant s as the coefficient of a
  distinguished unit variable (value nnrat/one). Re-presenting (a,(s,x)) as
  the next-variable constraint (a,(x,(s,nil))) and mapping it to the round's
  list form at the unit value (farkas-adapter-map-uppers ... one) gives the
  tail cons((s,one),nil), whose eval is s*1 + 0 ~ s. So

    lower: w <= a*x2 + s        ==>  w <= eval(cons(a,x2) cons((s,one),nil))
    upper: a*x2 + s <= b        ==>  eval(cons(a,x2) cons((s,one),nil)) <= b

  transporting each coupling across s ~ s*1 + 0 (multiply-one-right +
  add-zero-right). nnrat/farkas-vector-unit-column-lower and -upper fold this
  over the affine row lists: a satisfied affine system re-presents as a held
  next-variable system. This is a satisfaction-preserving representation
  bridge. The constant s already contains evaluated deeper-variable terms;
  the bridge does not restore those columns. The current recursion's Feasible
  predicate ignores its variable-count argument, and the round's existential
  output lacks source-row provenance. General n-variable elimination and dual
  extraction therefore remain unproved by this chain. Native proof data,
  axiom-free. See the design notes."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-vector-adapter-bilist :as vab]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as upper]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list-lower :as lower]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def lp (function/app (function/const* 'data/List [type-level]) pair-nn))

;; affine row (a,(s,x)) and next-variable constraint (coeff,(bound,(a2,rest)))
(def p2 (product nnrat nnrat))
(def arow (product nnrat p2))
(def list-arow (function/app (function/const* 'data/List [type-level]) arow))
(def n-ar (product nnrat lp))
(def n-br (product nnrat n-ar))
(def nvc (product nnrat n-br))
(def list-nvc (function/app (function/const* 'data/List [type-level]) nvc))

(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(def zero (function/const* 'nnrat/zero []))
(def one (function/const* 'nnrat/one []))
(defn- pair2 [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(def nil-pair (function/app (function/const* 'data/nil [type-level]) pair-nn))
(defn- cons-nvc [h t] (function/app (function/const* 'data/cons [type-level]) nvc h t))
(def nil-nvc (function/app (function/const* 'data/nil [type-level]) nvc))
(def nil-arow (function/app (function/const* 'data/nil [type-level]) arow))

(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- esym [l r same] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- etrans [l m r a b]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r a b))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- at-most-respects [l el r er sl sr ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ordered))
(defn- multiply-one-right [x] (function/app (function/const* 'nnrat/multiply-one-right []) x))
(defn- add-zero-right [x] (function/app (function/const* 'nnrat/add-zero-right []) x))

;; affine row projections
(defn- row-a [r] (fst nnrat p2 r))
(defn- row-s [r] (fst nnrat nnrat (snd nnrat p2 r)))
(defn- row-x [r] (snd nnrat nnrat (snd nnrat p2 r)))    ; w (lower) / b (upper)

;; re-present an affine row (a,(s,x)) as next-variable constraint (a,(x,(s,nil)))
(defn- repr-row [r]
  (pair2 nnrat n-br (row-a r)
         (pair2 nnrat n-ar (row-x r)
                (pair2 nnrat lp (row-s r) nil-pair))))

;; s ~ (s*one + zero)  (the unit-column value); etrans gives (s*one+0)~s, esym flips
(defn- s-eq [s]
  (esym (add (mul s one) zero) s
        (etrans (add (mul s one) zero) (mul s one) s
                (add-zero-right (mul s one))
                (multiply-one-right s))))

;; the round's per-row satisfied couplings (for naming conjuncts)
(defn- lower-coupling [r x2] (at-most (row-x r) (add (mul (row-a r) x2) (row-s r))))
(defn- upper-coupling [r x2] (at-most (add (mul (row-a r) x2) (row-s r)) (row-x r)))
;; the re-presented held forms (defeq to the map-uppers/lower-holds target)
(defn- unit-tail-eval [r x2]
  (add (mul (row-a r) x2) (add (mul (row-s r) one) zero)))

(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied []) rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied []) rows w))
(defn- lowers-hold [cs x2]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold []) cs x2))
(defn- uppers-hold [cs x2]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold []) cs x2))
(defn- map-uppers [lst x2]
  (function/app (function/const* 'nnrat/farkas-adapter-map-uppers []) lst x2))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))

;; the re-presentation map over an affine row list
(def repr-list-spec
  {:name 'nnrat/farkas-vector-unit-repr
   :kind :definition
   :universes []
   :type (function/arrow list-arow list-nvc)
   :value
   (function/lam
    [['rows list-arow]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     arow
     (function/lam [['ignored list-arow]] list-nvc)
     nil-nvc
     (function/lam
      [['head arow] ['tail list-arow] ['ih list-nvc]]
      (cons-nvc (repr-row 'head) 'ih))
     'rows))})

(def definition-specs [repr-list-spec])

(defn- repr-list [rows]
  (function/app (function/const* 'nnrat/farkas-vector-unit-repr []) rows))

(def unit-column-lower-spec
  {:name 'nnrat/farkas-vector-unit-column-lower
   :universes []
   :type
   (function/forall
    [['rows list-arow] ['x2 nnrat] ['h (lowers-sat 'rows 'x2)]]
    (lowers-hold (map-uppers (repr-list 'rows) one) 'x2))
   :value
   (function/lam
    [['rows list-arow] ['x2 nnrat] ['h (lowers-sat 'rows 'x2)]]
    (let [motive (function/lam
                  [['rs list-arow]]
                  (function/arrow (lowers-sat 'rs 'x2)
                                  (lowers-hold (map-uppers (repr-list 'rs) one) 'x2)))
          nil-case
          (function/lam [['hnil (lowers-sat nil-arow 'x2)]]
                        (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head arow] ['tail list-arow]
            ['ih (function/arrow (lowers-sat 'tail 'x2)
                                 (lowers-hold (map-uppers (repr-list 'tail) one) 'x2))]]
           (function/lam
            [['hcons (lowers-sat (function/app (function/const* 'data/cons [type-level]) arow 'head 'tail) 'x2)]]
            (let [hc (lower-coupling 'head 'x2)
                  ht (lowers-sat 'tail 'x2)
                  head-proof (left-conjunct hc ht 'hcons)
                  tail-proof (right-conjunct hc ht 'hcons)
                  ;; transport w <= a*x2 + s  to  w <= a*x2 + (s*one+0)
                  head-held (at-most-respects
                             (row-x 'head) (row-x 'head)
                             (unit-tail-eval 'head 'x2) (add (mul (row-a 'head) 'x2) (row-s 'head))
                             (erefl (row-x 'head))
                             (add-respects (mul (row-a 'head) 'x2) (mul (row-a 'head) 'x2)
                                           (add (mul (row-s 'head) one) zero) (row-s 'head)
                                           (erefl (mul (row-a 'head) 'x2))
                                           (esym (row-s 'head) (add (mul (row-s 'head) one) zero)
                                                 (s-eq (row-s 'head))))
                             head-proof)]
              (conjoin (at-most (row-x 'head) (unit-tail-eval 'head 'x2))
                       (lowers-hold (map-uppers (repr-list 'tail) one) 'x2)
                       head-held
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        arow motive nil-case cons-case 'rows)
       'h)))})

(def unit-column-upper-spec
  {:name 'nnrat/farkas-vector-unit-column-upper
   :universes []
   :type
   (function/forall
    [['rows list-arow] ['x2 nnrat] ['h (uppers-sat 'rows 'x2)]]
    (uppers-hold (map-uppers (repr-list 'rows) one) 'x2))
   :value
   (function/lam
    [['rows list-arow] ['x2 nnrat] ['h (uppers-sat 'rows 'x2)]]
    (let [motive (function/lam
                  [['rs list-arow]]
                  (function/arrow (uppers-sat 'rs 'x2)
                                  (uppers-hold (map-uppers (repr-list 'rs) one) 'x2)))
          nil-case
          (function/lam [['hnil (uppers-sat nil-arow 'x2)]]
                        (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head arow] ['tail list-arow]
            ['ih (function/arrow (uppers-sat 'tail 'x2)
                                 (uppers-hold (map-uppers (repr-list 'tail) one) 'x2))]]
           (function/lam
            [['hcons (uppers-sat (function/app (function/const* 'data/cons [type-level]) arow 'head 'tail) 'x2)]]
            (let [hc (upper-coupling 'head 'x2)
                  ht (uppers-sat 'tail 'x2)
                  head-proof (left-conjunct hc ht 'hcons)
                  tail-proof (right-conjunct hc ht 'hcons)
                  ;; transport a*x2 + s <= b  to  a*x2 + (s*one+0) <= b
                  head-held (at-most-respects
                             (unit-tail-eval 'head 'x2) (add (mul (row-a 'head) 'x2) (row-s 'head))
                             (row-x 'head) (row-x 'head)
                             (add-respects (mul (row-a 'head) 'x2) (mul (row-a 'head) 'x2)
                                           (add (mul (row-s 'head) one) zero) (row-s 'head)
                                           (erefl (mul (row-a 'head) 'x2))
                                           (esym (row-s 'head) (add (mul (row-s 'head) one) zero)
                                                 (s-eq (row-s 'head))))
                             (erefl (row-x 'head))
                             head-proof)]
              (conjoin (at-most (unit-tail-eval 'head 'x2) (row-x 'head))
                       (uppers-hold (map-uppers (repr-list 'tail) one) 'x2)
                       head-held
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        arow motive nil-case cons-case 'rows)
       'h)))})

(def theorem-specs [unit-column-lower-spec unit-column-upper-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      vab/extend-environment
      upper/extend-environment
      lower/extend-environment
      identities/extend-environment
      (support/extend-with :nnrat-farkas-vector-unit-column
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
