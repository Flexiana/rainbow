(ns rainbow.math.rational.nnrat.metric-separation
  "Exact separation for the computational NNRAT distance and finite radius.

  The raw NNRAT representation is a quotient presentation, so metric
  separation concludes `nnrat/equivalent`, not structural equality.  Scalar
  distance is zero exactly when its endpoints are equivalent.  The finite
  supremum radius is zero exactly when the functions are pointwise equivalent
  on every enumerated member; no claim is made outside that finite support.
  The distance is also a congruence for the quotient: replacing either
  endpoint by an equivalent value keeps the distance equivalent.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness
             :as legacy-separation]
            [rainbow.math.finite.metric-separation :as nat-separation]
            [rainbow.math.finite.nnrat-sup-radius :as radius]
            [rainbow.math.finite.policy-iteration :as policy-order]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.bellman-value-optimality :as optimality]
            [rainbow.math.rational.nnrat.add-monotone :as monotone-add]
            [rainbow.math.rational.nnrat.additive-reassociation
             :as additive-reassociation]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.nnrat.distributive :as distributive]
            [rainbow.math.rational.nnrat.multiply-monotone :as monotone-mul]
            [rainbow.math.rational.nnrat.farkas-elim-list :as nnrat-bounds]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.list-sum :as list-sum]
            [rainbow.math.rational.nnrat.map-sum-distance :as sum-distance]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def type-level [:succ [:zero]])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U])
       element source value))
(defn- nnum [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- den [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- finite-radius [element source left right]
  (app (function/const* 'metric/finite-nnrat-sup-radius [U])
       element source left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'nnrat/equivalent-to-at-most [])
       left right same))
(defn- order-reflexive [value]
  (app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- order-respects
  [left equivalent-left right equivalent-right
   same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left equivalent-left right equivalent-right
       same-left same-right ordered))
(defn- to-cross [left right ordered]
  (app (function/const* 'nnrat/at-most-to-cross [])
       left right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'nnrat/at-most-antisymmetric [])
       left right left-right right-left))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def at-most-antisymmetric-spec
  {:name 'nnrat/at-most-antisymmetric
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['left-right (rle 'left 'right)]
     ['right-left (rle 'right 'left)]]
    (req 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['left-right (rle 'left 'right)]
     ['right-left (rle 'right 'left)]]
    (let [left-cross (nmul (nnum 'left) (den 'right))
          right-cross (nmul (nnum 'right) (den 'left))]
      (app (function/const* 'nat/at-most-antisymmetric [])
           left-cross right-cross
           (to-cross 'left 'right 'left-right)
           (to-cross 'right 'left 'right-left))))})

(def distance-at-most-zero-of-equivalent-spec
  {:name 'nnrat/distance-at-most-zero-of-equivalent
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (rle (scalar-distance 'left 'right) nnrat-zero))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (let [right-same-left
          (equivalent-symmetric 'left 'right 'same)
          left-right
          (equivalent-to-at-most 'left 'right 'same)
          right-left
          (equivalent-to-at-most 'right 'left right-same-left)
          left-close
          (order-respects
           'left 'left (radd 'right nnrat-zero) 'right
           (equivalent-reflexive 'left)
           (app (function/const* 'nnrat/add-zero-right []) 'right)
           left-right)
          right-close
          (order-respects
           'right 'right (radd 'left nnrat-zero) 'left
           (equivalent-reflexive 'right)
           (app (function/const* 'nnrat/add-zero-right []) 'left)
           right-left)]
      (app
       (function/const* 'nnrat/distance-at-most-of-additive-closeness [])
       'left 'right nnrat-zero left-close right-close)))})

(def distance-zero-of-equivalent-spec
  {:name 'nnrat/distance-zero-of-equivalent
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (req (scalar-distance 'left 'right) nnrat-zero))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (let [distance (scalar-distance 'left 'right)]
      (antisymmetric
       distance nnrat-zero
       (app
        (function/const* 'nnrat/distance-at-most-zero-of-equivalent [])
        'left 'right 'same)
       (app (function/const* 'nnrat/zero-at-most []) distance))))})

(def equivalent-of-distance-at-most-zero-spec
  {:name 'nnrat/equivalent-of-distance-at-most-zero
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['distance-at-most-zero
      (rle (scalar-distance 'left 'right) nnrat-zero)]]
    (req 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['distance-at-most-zero
      (rle (scalar-distance 'left 'right) nnrat-zero)]]
    (let [closeness
          (app
           (function/const* 'nnrat/additive-closeness-of-distance-at-most [])
           'left 'right nnrat-zero 'distance-at-most-zero)
          left-padded
          (rle 'left (radd 'right nnrat-zero))
          right-padded
          (rle 'right (radd 'left nnrat-zero))
          left-right
          (order-respects
           'left 'left 'right (radd 'right nnrat-zero)
           (equivalent-reflexive 'left)
           (equivalent-symmetric
            (radd 'right nnrat-zero) 'right
            (app (function/const* 'nnrat/add-zero-right []) 'right))
           (left-conjunct left-padded right-padded closeness))
          right-left
          (order-respects
           'right 'right 'left (radd 'left nnrat-zero)
           (equivalent-reflexive 'right)
           (equivalent-symmetric
            (radd 'left nnrat-zero) 'left
            (app (function/const* 'nnrat/add-zero-right []) 'left))
           (right-conjunct left-padded right-padded closeness))]
      (antisymmetric 'left 'right left-right right-left)))})

(def equivalent-of-distance-zero-spec
  {:name 'nnrat/equivalent-of-distance-zero
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['distance-zero
      (req (scalar-distance 'left 'right) nnrat-zero)]]
    (req 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['distance-zero
      (req (scalar-distance 'left 'right) nnrat-zero)]]
    (app
     (function/const* 'nnrat/equivalent-of-distance-at-most-zero [])
     'left 'right
     (equivalent-to-at-most
      (scalar-distance 'left 'right) nnrat-zero 'distance-zero)))})

(def distance-zero-iff-equivalent-spec
  {:name 'nnrat/distance-zero-iff-equivalent
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]]
    (proposition/equivalence
     (req (scalar-distance 'left 'right) nnrat-zero)
     (req 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [distance-zero
          (req (scalar-distance 'left 'right) nnrat-zero)
          same (req 'left 'right)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       distance-zero same
       (function/lam
        [['zero-distance distance-zero]]
        (app (function/const* 'nnrat/equivalent-of-distance-zero [])
             'left 'right 'zero-distance))
       (function/lam
        [['equivalent same]]
        (app (function/const* 'nnrat/distance-zero-of-equivalent [])
             'left 'right 'equivalent)))))})

(defn- add-respects [l l-eq r r-eq same-l same-r]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       l l-eq r r-eq same-l same-r))

(defn- distance-at-most-of-closeness
  "distance a b <= radius, from the two padded inequalities."
  [a b radius left-close right-close]
  (app (function/const* 'nnrat/distance-at-most-of-additive-closeness [])
       a b radius left-close right-close))

(defn- distance-dominates
  "distance a b <= distance a-eq b-eq, given a ~ a-eq and b ~ b-eq. The
  dominating distance bounds its own endpoints by additive closeness, and
  each padded inequality transports along the endpoint equivalences."
  [a a-eq b b-eq same-a same-b]
  (let [radius (scalar-distance a-eq b-eq)
        left-padded (rle a-eq (radd b-eq radius))
        right-padded (rle b-eq (radd a-eq radius))
        closeness
        (app
         (function/const* 'nnrat/additive-closeness-of-distance-at-most [])
         a-eq b-eq radius (order-reflexive radius))
        radius-same (equivalent-reflexive radius)
        left-close
        (order-respects
         a a-eq (radd b radius) (radd b-eq radius)
         same-a (add-respects b b-eq radius radius same-b radius-same)
         (left-conjunct left-padded right-padded closeness))
        right-close
        (order-respects
         b b-eq (radd a radius) (radd a-eq radius)
         same-b (add-respects a a-eq radius radius same-a radius-same)
         (right-conjunct left-padded right-padded closeness))]
    (distance-at-most-of-closeness a b radius left-close right-close)))

(def distance-respects-equivalence-spec
  {:name 'nnrat/distance-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left nnrat] ['equivalent-left nnrat]
     ['right nnrat] ['equivalent-right nnrat]
     ['same-left (req 'left 'equivalent-left)]
     ['same-right (req 'right 'equivalent-right)]]
    (req (scalar-distance 'left 'right)
         (scalar-distance 'equivalent-left 'equivalent-right)))
   :value
   (function/lam
    [['left nnrat] ['equivalent-left nnrat]
     ['right nnrat] ['equivalent-right nnrat]
     ['same-left (req 'left 'equivalent-left)]
     ['same-right (req 'right 'equivalent-right)]]
    (antisymmetric
     (scalar-distance 'left 'right)
     (scalar-distance 'equivalent-left 'equivalent-right)
     (distance-dominates
      'left 'equivalent-left 'right 'equivalent-right
      'same-left 'same-right)
     (distance-dominates
      'equivalent-left 'left 'equivalent-right 'right
      (equivalent-symmetric 'left 'equivalent-left 'same-left)
      (equivalent-symmetric 'right 'equivalent-right 'same-right))))})

(defn- list-of [element]
  (app (function/const* 'data/List [data-u]) element))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- add-monotone [a a-hi b b-hi ha hb]
  (app (function/const* 'nnrat/add-monotone []) a a-hi b b-hi ha hb))
(defn- add-left-monotone [fixed b b-hi hb]
  (app (function/const* 'nnrat/add-left-monotone []) fixed b b-hi hb))
(defn- add-four-reorder [a b c d]
  (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- closeness-of-distance [a b radius bounded]
  (app (function/const* 'nnrat/additive-closeness-of-distance-at-most [])
       a b radius bounded))

(def distance-add-subadditive-spec
  "The scalar triangle step under addition: the distance between two sums
  is at most the sum of the componentwise distances. Proved entirely
  through the additive-closeness interface -- each component's distance
  bounds its own endpoints, the padded inequalities add by monotonicity,
  and one four-term reorder collects the radii."
  {:name 'nnrat/distance-add-subadditive
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (rle (scalar-distance (radd 'a 'b) (radd 'c 'd))
         (radd (scalar-distance 'a 'c) (scalar-distance 'b 'd))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (let [first-radius (scalar-distance 'a 'c)
          second-radius (scalar-distance 'b 'd)
          radius (radd first-radius second-radius)
          first-left (rle 'a (radd 'c first-radius))
          first-right (rle 'c (radd 'a first-radius))
          second-left (rle 'b (radd 'd second-radius))
          second-right (rle 'd (radd 'b second-radius))
          first-close
          (closeness-of-distance 'a 'c first-radius
                                 (order-reflexive first-radius))
          second-close
          (closeness-of-distance 'b 'd second-radius
                                 (order-reflexive second-radius))
          left-padded
          (add-monotone 'a (radd 'c first-radius)
                        'b (radd 'd second-radius)
                        (left-conjunct first-left first-right first-close)
                        (left-conjunct second-left second-right second-close))
          right-padded
          (add-monotone 'c (radd 'a first-radius)
                        'd (radd 'b second-radius)
                        (right-conjunct first-left first-right first-close)
                        (right-conjunct second-left second-right second-close))
          left-close
          (order-respects
           (radd 'a 'b) (radd 'a 'b)
           (radd (radd 'c 'd) radius)
           (radd (radd 'c first-radius) (radd 'd second-radius))
           (equivalent-reflexive (radd 'a 'b))
           (equivalent-symmetric
            (radd (radd 'c first-radius) (radd 'd second-radius))
            (radd (radd 'c 'd) radius)
            (add-four-reorder 'c first-radius 'd second-radius))
           left-padded)
          right-close
          (order-respects
           (radd 'c 'd) (radd 'c 'd)
           (radd (radd 'a 'b) radius)
           (radd (radd 'a first-radius) (radd 'b second-radius))
           (equivalent-reflexive (radd 'c 'd))
           (equivalent-symmetric
            (radd (radd 'a first-radius) (radd 'b second-radius))
            (radd (radd 'a 'b) radius)
            (add-four-reorder 'a first-radius 'b second-radius))
           right-padded)]
      (distance-at-most-of-closeness
       (radd 'a 'b) (radd 'c 'd) radius left-close right-close)))})

(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- multiply-monotone [factor a b ordered]
  (app (function/const* 'nnrat/multiply-monotone []) factor a b ordered))
(defn- distributes-left [factor left right]
  (app (function/const* 'nnrat/multiply-distributes-add-left [])
       factor left right))

(def distance-multiply-left-bound-spec
  "Multiplicative distance scaling, the bound direction the residual
  expansion consumes: scaling both endpoints by a common factor scales
  the distance by at most that factor. Through the additive-closeness
  interface: the unscaled closeness inequalities multiply through by
  monotonicity, and left distributivity re-shapes each padded product
  into a padded sum."
  {:name 'nnrat/distance-multiply-left-bound
   :universes []
   :type
   (function/forall
    [['factor nnrat] ['left nnrat] ['right nnrat]]
    (rle (scalar-distance (rmul 'factor 'left) (rmul 'factor 'right))
         (rmul 'factor (scalar-distance 'left 'right))))
   :value
   (function/lam
    [['factor nnrat] ['left nnrat] ['right nnrat]]
    (let [epsilon (scalar-distance 'left 'right)
          radius (rmul 'factor epsilon)
          left-padded (rle 'left (radd 'right epsilon))
          right-padded (rle 'right (radd 'left epsilon))
          closeness
          (closeness-of-distance 'left 'right epsilon
                                 (order-reflexive epsilon))
          left-close
          (order-respects
           (rmul 'factor 'left) (rmul 'factor 'left)
           (radd (rmul 'factor 'right) radius)
           (rmul 'factor (radd 'right epsilon))
           (equivalent-reflexive (rmul 'factor 'left))
           (equivalent-symmetric
            (rmul 'factor (radd 'right epsilon))
            (radd (rmul 'factor 'right) radius)
            (distributes-left 'factor 'right epsilon))
           (multiply-monotone
            'factor 'left (radd 'right epsilon)
            (left-conjunct left-padded right-padded closeness)))
          right-close
          (order-respects
           (rmul 'factor 'right) (rmul 'factor 'right)
           (radd (rmul 'factor 'left) radius)
           (rmul 'factor (radd 'left epsilon))
           (equivalent-reflexive (rmul 'factor 'right))
           (equivalent-symmetric
            (rmul 'factor (radd 'left epsilon))
            (radd (rmul 'factor 'left) radius)
            (distributes-left 'factor 'left epsilon))
           (multiply-monotone
            'factor 'right (radd 'left epsilon)
            (right-conjunct left-padded right-padded closeness)))]
      (distance-at-most-of-closeness
       (rmul 'factor 'left) (rmul 'factor 'right) radius
       left-close right-close)))})

(def map-sum-distance-bound-spec
  "The plain bound specializes the general radius theorem; the independent
  induction proof from 14a7a53 is retained in the test fixture."
  sum-distance/map-sum-distance-bound-spec)

(defn- list-membership [element itemsv value]
  (app (function/const* 'list/membership [U]) element itemsv value))
(defn- data-equality [element left right]
  (function/equality data-u element left right))
(defn- data-reflexive [element value]
  (app (function/const* 'equality/reflexive [data-u]) element value))
(defn- left-disjunct-intro [left-prop right-prop evidence]
  (app (function/const* 'proposition/left-disjunct [])
       left-prop right-prop evidence))
(defn- right-disjunct-intro [left-prop right-prop evidence]
  (app (function/const* 'proposition/right-disjunct [])
       left-prop right-prop evidence))
(defn- add-monotone-full [a a-hi b b-hi ha hb]
  (app (function/const* 'nnrat/add-monotone []) a a-hi b b-hi ha hb))

(def map-sum-monotone-on-spec
  "Member-restricted sum monotonicity: if f is below g at every LISTED
  element, the sums are ordered -- the pointwise premise is demanded only
  on members, unlike nnrat/map-sum-monotone's all-elements form. List
  induction with the hypothesis threaded through the motive; the head
  uses the left disjunct of cons-membership, the tail restricts the
  hypothesis along the right disjunct."
  {:name 'nnrat/map-sum-monotone-on :universes ['u]
   :type
   (function/forall
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['g (function/arrow 'A nnrat)]
     ['items (list-of 'A)]
     ['bounded (function/forall
                [['value 'A]
                 ['member (list-membership 'A 'items 'value)]]
                (rle (app 'f 'value) (app 'g 'value)))]]
    (rle (map-sum 'A 'f 'items) (map-sum 'A 'g 'items)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['g (function/arrow 'A nnrat)]
     ['items (list-of 'A)]]
    (app
     (function/const* 'data/List.rec [data-u [:zero]])
     'A
     (function/lam
      [['current (list-of 'A)]]
      (function/arrow
       (function/forall
        [['value 'A]
         ['member (list-membership 'A 'current 'value)]]
        (rle (app 'f 'value) (app 'g 'value)))
       (rle (map-sum 'A 'f 'current) (map-sum 'A 'g 'current))))
     (function/lam
      [['bounded (function/forall
                  [['value 'A] ['member (proposition/falsity)]]
                  (rle (app 'f 'value) (app 'g 'value)))]]
      (order-reflexive nnrat-zero))
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['sound (function/arrow
                (function/forall
                 [['value 'A]
                  ['member (list-membership 'A 'tail 'value)]]
                 (rle (app 'f 'value) (app 'g 'value)))
                (rle (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)))]
       ['bounded (function/forall
                  [['value 'A]
                   ['member (proposition/disjunction
                             (data-equality 'A 'value 'head)
                             (list-membership 'A 'tail 'value))]]
                  (rle (app 'f 'value) (app 'g 'value)))]]
      (let [head-bound
            (app 'bounded 'head
                 (left-disjunct-intro
                  (data-equality 'A 'head 'head)
                  (list-membership 'A 'tail 'head)
                  (data-reflexive 'A 'head)))
            tail-bound
            (app 'sound
                 (function/lam
                  [['value 'A]
                   ['member (list-membership 'A 'tail 'value)]]
                  (app 'bounded 'value
                       (right-disjunct-intro
                        (data-equality 'A 'value 'head)
                        (list-membership 'A 'tail 'value)
                        'member))))]
        (add-monotone-full
         (app 'f 'head) (app 'g 'head)
         (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
         head-bound tail-bound)))
     'items))})

(def finite-radius-zero-of-pointwise-equivalent-spec
  {:name 'metric/finite-nnrat-sup-radius-zero-of-pointwise-equivalent
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (req (app 'left 'state) (app 'right 'state)))]]
    (req (finite-radius 'A 'source 'left 'right) nnrat-zero))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (req (app 'left 'state) (app 'right 'state)))]]
    (let [sup-radius (finite-radius 'A 'source 'left 'right)
          radius-at-most-zero
          (app
           (function/const* 'metric/finite-nnrat-sup-radius-bounded [U])
           'A 'source 'left 'right nnrat-zero
           (order-reflexive nnrat-zero)
           (function/lam
            [['state 'A]
             ['member (source-membership 'A 'source 'state)]]
            (app
             (function/const*
              'nnrat/distance-at-most-zero-of-equivalent [])
             (app 'left 'state) (app 'right 'state)
             (app 'pointwise 'state 'member))))
          zero-at-most-radius
          (app
           (function/const*
            'metric/finite-nnrat-sup-radius-nonnegative [U])
           'A 'source 'left 'right)]
      (antisymmetric
       sup-radius nnrat-zero
       radius-at-most-zero zero-at-most-radius)))})

(def pointwise-equivalent-of-finite-radius-zero-spec
  {:name 'metric/pointwise-equivalent-of-finite-nnrat-sup-radius-zero
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]
     ['radius-zero
      (req (finite-radius 'A 'source 'left 'right) nnrat-zero)]]
    (function/forall
     [['state 'A]
      ['member (source-membership 'A 'source 'state)]]
     (req (app 'left 'state) (app 'right 'state))))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nnrat)]
     ['right (function/arrow 'A nnrat)]
     ['radius-zero
      (req (finite-radius 'A 'source 'left 'right) nnrat-zero)]]
    (function/lam
     [['state 'A]
      ['member (source-membership 'A 'source 'state)]]
     (let [distance
           (scalar-distance (app 'left 'state) (app 'right 'state))
           sup-radius (finite-radius 'A 'source 'left 'right)
           distance-at-most-radius
           (app
            (function/const*
             'metric/finite-nnrat-sup-radius-upper-bound [U])
            'A 'source 'left 'right 'state 'member)
           distance-at-most-zero
           (order-respects
            distance distance nnrat-zero sup-radius
            (equivalent-reflexive distance)
            (equivalent-symmetric sup-radius nnrat-zero 'radius-zero)
            distance-at-most-radius)]
       (app
        (function/const* 'nnrat/equivalent-of-distance-at-most-zero [])
        (app 'left 'state) (app 'right 'state)
        distance-at-most-zero))))})

(def finite-radius-zero-iff-pointwise-equivalent-spec
  (let [pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (req (app 'left 'state) (app 'right 'state)))
        radius-zero
        (req (finite-radius 'A 'source 'left 'right) nnrat-zero)]
    {:name 'metric/finite-nnrat-sup-radius-zero-iff-pointwise-equivalent
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]]
      (proposition/equivalence radius-zero pointwise))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]]
      (app
       (function/const* 'proposition/equivalence-intro [])
       radius-zero pointwise
       (function/lam
        [['zero-radius radius-zero]]
        (app
         (function/const*
          'metric/pointwise-equivalent-of-finite-nnrat-sup-radius-zero
          [U])
         'A 'source 'left 'right 'zero-radius))
       (function/lam
        [['same pointwise]]
        (app
         (function/const*
          'metric/finite-nnrat-sup-radius-zero-of-pointwise-equivalent
          [U])
         'A 'source 'left 'right 'same))))}))

(def definition-specs [])
(def theorem-specs
  [at-most-antisymmetric-spec
   distance-at-most-zero-of-equivalent-spec
   distance-zero-of-equivalent-spec
   equivalent-of-distance-at-most-zero-spec
   equivalent-of-distance-zero-spec
   distance-zero-iff-equivalent-spec
   distance-respects-equivalence-spec
   distance-add-subadditive-spec
   distance-multiply-left-bound-spec
   map-sum-distance-bound-spec
   map-sum-monotone-on-spec
   finite-radius-zero-of-pointwise-equivalent-spec
   pointwise-equivalent-of-finite-radius-zero-spec
   finite-radius-zero-iff-pointwise-equivalent-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-radius-if-missing [env]
  (if (environment/resolve-id env 'metric/finite-nnrat-sup-radius)
    env
    (radius/extend-environment env)))

(defn extend-environment [env]
  (-> env
      extend-radius-if-missing
      sum-distance/extend-unweighted-environment
      (extend-spec-if-missing
       'nat/equal-zero-of-at-most-zero :finite-metric-separation
       nat-separation/equal-zero-of-at-most-zero-spec)
      (extend-spec-if-missing
       'nat/at-most-antisymmetric
       :bellman-scaled-fixed-point-uniqueness
       legacy-separation/at-most-antisymmetric-spec)
      (extend-spec-if-missing
       'nnrat/equivalent-to-at-most :finite-policy-iteration
       policy-order/equivalent-to-at-most-spec)
      (extend-spec-if-missing
       'nnrat/add-zero-right :nnrat-identities
       identities/add-zero-right-spec)
      (extend-spec-if-missing
       'nnrat/zero-at-most :nnrat-farkas-elim-list
       nnrat-bounds/zero-at-most-spec)
      (extend-spec-if-missing
       'nnrat/add-right-monotone-base :nnrat-add-monotone
       monotone-add/add-right-monotone-base-spec)
      (extend-spec-if-missing
       'nnrat/add-right-monotone :nnrat-add-monotone
       monotone-add/add-right-monotone-spec)
      (extend-spec-if-missing
       'nnrat/add-commutative :nnrat-add-monotone
       monotone-add/add-commutative-spec)
      (extend-spec-if-missing
       'nnrat/add-left-monotone :nnrat-add-monotone
       monotone-add/add-left-monotone-spec)
      (extend-spec-if-missing
       'nnrat/add-monotone :nnrat-add-monotone
       monotone-add/add-monotone-spec)
      (extend-spec-if-missing
       'nnrat/add-associative :nnrat-additive-reassociation
       additive-reassociation/add-associative-spec)
      (extend-spec-if-missing
       'nnrat/add-swap-right :nnrat-additive-reassociation
       additive-reassociation/add-swap-right-spec)
      (extend-spec-if-missing
       'nnrat/add-four-reorder :nnrat-additive-reassociation
       additive-reassociation/add-four-reorder-spec)
      ;; Only the definition: the bound's proof needs map-sum to unfold,
      ;; not its laws, and entering the whole list-sum world here would
      ;; replay its unguarded add-monotone chain against the specs above.
      (extend-spec-if-missing
       'nnrat/map-sum :nnrat-list-sum list-sum/map-sum-spec)
      (extend-spec-if-missing
       'nnrat/multiply-monotone-base :nnrat-multiply-monotone
       monotone-mul/multiply-monotone-base-spec)
      (extend-spec-if-missing
       'nnrat/multiply-monotone :nnrat-multiply-monotone
       monotone-mul/multiply-monotone-spec)
      (extend-spec-if-missing
       'nnrat/multiply-commutative :nnrat-commutative
       commutative/multiply-commutative-spec)
      (extend-spec-if-missing
       'nnrat/multiply-distributes-add-right :nnrat-distributive
       distributive/multiply-distributes-add-right-spec)
      (extend-spec-if-missing
       'nnrat/multiply-distributes-add-left :finite-bellman-value-optimality
       optimality/multiply-distributes-add-left-spec)
      (support/extend-with :nnrat-metric-separation theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
