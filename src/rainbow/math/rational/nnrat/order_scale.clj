(ns rainbow.math.rational.nnrat.order-scale
  "Positive scaling and coefficient normalization for the nnrat order.

  Positivity is represented structurally: a positive coefficient has the form
  `nnrat/make (data/succ ap) adp`.  The central cancellation proof descends from
  `nnrat/at-most` to its natural-number cross product, normalizes the product,
  and cancels the positive numerator and denominator factors.  Division then
  turns upper and lower coefficient constraints into ordinary bound predicates.
  The proper-fraction rate-null law closes the family: a value at most a
  proper multiple of itself is equivalent to zero.

  Native and axiom-free on the d63 checkpoint."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness
             :as legacy-separation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.multiply-commute :as commute]
            [rainbow.math.rational.nnrat.multiply-monotone :as monotone]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.nat.metric-separation :as nat-separation]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.logic.strict-contraction-uniqueness
             :as strict-uniqueness]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- denominator-predecessor [value]
  (function/app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- combine [left right]
  (function/app
   (function/const* 'nnrat/combine-denominator-predecessors [])
   left right))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- reciprocal [value]
  (function/app (function/const* 'nnrat/reciprocal []) value))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- to-cross [left right ordered]
  (function/app (function/const* 'nnrat/at-most-to-cross [])
                left right ordered))
(defn- from-cross [left right ordered]
  (function/app (function/const* 'nnrat/at-most-from-cross [])
                left right ordered))
(defn- denominator-combine [left right]
  (function/app (function/const* 'nnrat/denominator-combine [])
                left right))
(defn- equality-symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))
(defn- equality-congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left [])
                left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right [])
                left right replacement same ordered))
(defn- multiply-right-cancel [left right predecessor ordered]
  (function/app
   (function/const* 'nat/at-most-multiply-right-cancel [])
   left right predecessor ordered))
(defn- ring-equality [left right]
  (:proof (ring/prove-nat-eq left right)))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))
(defn- equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- multiply-respects [left equivalent-left right equivalent-right
                          same-left same-right]
  (function/app
   (function/const* 'nnrat/multiply-respects-equivalence [])
   left equivalent-left right equivalent-right same-left same-right))
(defn- at-most-respects [left equivalent-left right equivalent-right
                         same-left same-right ordered]
  ;; `ordered` is deliberately on the equivalent versions.
  (function/app
   (function/const* 'nnrat/at-most-respects-equivalence [])
   left equivalent-left right equivalent-right
   same-left same-right ordered))

(def nat-zero (function/const* 'data/zero []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- add-nat [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- nat-at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))
(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- use-witness [predicate target evidence handler]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nat predicate target evidence handler))
(defn- witness [predicate value proof]
  (function/app (function/const* 'proposition/witness [type-level])
                nat predicate value proof))
(defn- equality-transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))
(defn- equality-reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat value))
(defn- strict-monotone [factor left right ordered factor-positive]
  (function/app
   (function/const* 'nat/multiply-right-strict-monotone-positive [])
   factor left right ordered factor-positive))
(defn- at-most-strict-transitive [left middle right first second]
  (function/app
   (function/const* 'nat/at-most-strict-below-transitive [])
   left middle right first second))

;; If c is positive, c*v <= c*w implies v <= w.  At the cross-product level,
;; both sides contain the numerator succ(ap) and denominator succ(adp) of c.
(def at-most-multiply-left-cancel-spec
  {:name 'nnrat/at-most-multiply-left-cancel :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['v nnrat] ['w nnrat]
     ['ordered
      (at-most (multiply (make (succ 'ap) 'adp) 'v)
               (multiply (make (succ 'ap) 'adp) 'w))]]
    (at-most 'v 'w))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['v nnrat] ['w nnrat]
     ['ordered
      (at-most (multiply (make (succ 'ap) 'adp) 'v)
               (multiply (make (succ 'ap) 'adp) 'w))]]
    (let [c (make (succ 'ap) 'adp)
          nc (succ 'ap)
          dc (succ 'adp)
          nv (numerator 'v)
          nw (numerator 'w)
          dvp (denominator-predecessor 'v)
          dwp (denominator-predecessor 'w)
          dv (denominator 'v)
          dw (denominator 'w)
          cv (multiply c 'v)
          cw (multiply c 'w)
          dcv (succ (combine 'adp dvp))
          dcw (succ (combine 'adp dwp))
          left-expanded (multiply-nat (multiply-nat nc nv)
                                      (multiply-nat dc dw))
          right-expanded (multiply-nat (multiply-nat nc nw)
                                       (multiply-nat dc dv))
          left-normal (multiply-nat
                       (multiply-nat (multiply-nat nv dw) dc) nc)
          right-normal (multiply-nat
                        (multiply-nat (multiply-nat nw dv) dc) nc)
          cross (to-cross cv cw 'ordered)
          left-denominator-same
          (equality-congruent
           (function/lam [['candidate nat]]
                         (multiply-nat (multiply-nat nc nv) 'candidate))
           dcw (multiply-nat dc dw)
           (denominator-combine 'adp dwp))
          replace-left-denominator
          (rewrite-left
           left-expanded
           (multiply-nat (multiply-nat nc nv) dcw)
           (multiply-nat (multiply-nat nc nw) dcv)
           (equality-symmetric
            (multiply-nat (multiply-nat nc nv) dcw)
            left-expanded left-denominator-same)
           cross)
          right-denominator-same
          (equality-congruent
           (function/lam [['candidate nat]]
                         (multiply-nat (multiply-nat nc nw) 'candidate))
           dcv (multiply-nat dc dv)
           (denominator-combine 'adp dvp))
          replace-right-denominator
          (rewrite-right
           left-expanded
           (multiply-nat (multiply-nat nc nw) dcv)
           right-expanded right-denominator-same
           replace-left-denominator)
          normalize-left
          (rewrite-left left-normal left-expanded right-expanded
                        (ring-equality left-normal left-expanded)
                        replace-right-denominator)
          normalize-right
          (rewrite-right left-normal right-expanded right-normal
                         (ring-equality right-expanded right-normal)
                         normalize-left)
          cancel-numerator
          (multiply-right-cancel
           (multiply-nat (multiply-nat nv dw) dc)
           (multiply-nat (multiply-nat nw dv) dc)
           'ap normalize-right)
          cancel-denominator
          (multiply-right-cancel
           (multiply-nat nv dw) (multiply-nat nw dv)
           'adp cancel-numerator)]
      (from-cross 'v 'w cancel-denominator)))})

;; For positive a, multiplying b/a by a recovers b up to rational equivalence.
(def multiply-divide-cancel-spec
  {:name 'nnrat/multiply-divide-cancel :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['b nnrat]]
    (equivalent
     (multiply (make (succ 'ap) 'adp)
               (divide 'b (make (succ 'ap) 'adp)))
     'b))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['b nnrat]]
    (let [a (make (succ 'ap) 'adp)
          inverse (reciprocal a)
          start (multiply a (divide 'b a))
          associated (multiply (multiply a 'b) inverse)
          swapped (multiply (multiply a inverse) 'b)
          one-times-b (multiply nnrat-one 'b)
          unassociate
          (equivalent-symmetric
           associated (multiply a (multiply 'b inverse))
           (function/app
            (function/const* 'nnrat/multiply-associative [])
            a 'b inverse))
          swap
          (function/app (function/const* 'nnrat/multiply-swap-right [])
                        a 'b inverse)
          inverse-cancels
          (function/app (function/const* 'nnrat/divide-self-positive [])
                        'ap 'adp)
          replace-inverse
          (multiply-respects
           (multiply a inverse) nnrat-one 'b 'b
           inverse-cancels (equivalent-reflexive 'b))
          remove-one
          (function/app (function/const* 'nnrat/multiply-one-left []) 'b)
          through-association
          (equivalent-transitive start associated swapped
                                 unassociate swap)
          through-cancellation
          (equivalent-transitive start swapped one-times-b
                                 through-association replace-inverse)]
      (equivalent-transitive start one-times-b 'b
                             through-cancellation remove-one)))})

;; a*v <= b  <->  v <= b/a, for a represented by a positive numerator.
(def normalize-upper-spec
  {:name 'nnrat/at-most-multiply-left-normalize-upper :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['v nnrat] ['b nnrat]]
    (let [a (make (succ 'ap) 'adp)]
      (proposition/equivalence
       (at-most (multiply a 'v) 'b)
       (at-most 'v (divide 'b a)))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['v nnrat] ['b nnrat]]
    (let [a (make (succ 'ap) 'adp)
          quotient (divide 'b a)
          scaled-v (multiply a 'v)
          scaled-quotient (multiply a quotient)
          original (at-most scaled-v 'b)
          normalized (at-most 'v quotient)
          cancellation
          (function/app (function/const* 'nnrat/multiply-divide-cancel [])
                        'ap 'adp 'b)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       original normalized
       (function/lam
        [['ordered original]]
        (let [scaled
              (at-most-respects
               scaled-v scaled-v scaled-quotient 'b
               (equivalent-reflexive scaled-v) cancellation 'ordered)]
          (function/app
           (function/const* 'nnrat/at-most-multiply-left-cancel [])
           'ap 'adp 'v quotient scaled)))
       (function/lam
        [['ordered normalized]]
        (let [scaled
              (function/app (function/const* 'nnrat/multiply-monotone [])
                            a 'v quotient 'ordered)]
          (at-most-respects
           scaled-v scaled-v 'b scaled-quotient
           (equivalent-reflexive scaled-v)
           (equivalent-symmetric scaled-quotient 'b cancellation)
           scaled))))))})

;; b <= a*v  <->  b/a <= v, the lower-bound orientation of normalization.
(def normalize-lower-spec
  {:name 'nnrat/at-most-multiply-left-normalize-lower :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['b nnrat] ['v nnrat]]
    (let [a (make (succ 'ap) 'adp)]
      (proposition/equivalence
       (at-most 'b (multiply a 'v))
       (at-most (divide 'b a) 'v))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['b nnrat] ['v nnrat]]
    (let [a (make (succ 'ap) 'adp)
          quotient (divide 'b a)
          scaled-v (multiply a 'v)
          scaled-quotient (multiply a quotient)
          original (at-most 'b scaled-v)
          normalized (at-most quotient 'v)
          cancellation
          (function/app (function/const* 'nnrat/multiply-divide-cancel [])
                        'ap 'adp 'b)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       original normalized
       (function/lam
        [['ordered original]]
        (let [scaled
              (at-most-respects
               scaled-quotient 'b scaled-v scaled-v
               cancellation (equivalent-reflexive scaled-v) 'ordered)]
          (function/app
           (function/const* 'nnrat/at-most-multiply-left-cancel [])
           'ap 'adp quotient 'v scaled)))
       (function/lam
        [['ordered normalized]]
        (let [scaled
              (function/app (function/const* 'nnrat/multiply-monotone [])
                            a quotient 'v 'ordered)]
          (at-most-respects
           'b scaled-quotient scaled-v scaled-v
           (equivalent-symmetric scaled-quotient 'b cancellation)
           (equivalent-reflexive scaled-v) scaled))))))})

;; A value at most a PROPER-fraction multiple of itself is zero.  The proper
;; coefficient is structural: np/(dp+1) with np <= dp.  At the cross-product
;; level the bound becomes (dp+1)*m <= np*m for m = numerator(x)*denominator(x);
;; if the numerator were positive, m would be positive and strict multiplication
;; monotonicity would put (dp+1)*m strictly above np*m, a self-strict-below.
;; So the numerator is zero and x is equivalent to zero.  This is the rate-null
;; joint of the ergodic assembly: the Dobrushin contraction inequality at two
;; stationary distributions leaves exactly this premise on the total variation.
(def zero-of-proper-contraction-spec
  {:name 'nnrat/zero-of-proper-contraction :universes []
   :type
   (function/forall
    [['np nat] ['dp nat] ['x nnrat]
     ['proper (nat-at-most 'np 'dp)]
     ['bounded (at-most 'x (multiply (make 'np 'dp) 'x))]]
    (equivalent 'x nnrat-zero))
   :value
   (function/lam
    [['np nat] ['dp nat] ['x nnrat]
     ['proper (nat-at-most 'np 'dp)]
     ['bounded (at-most 'x (multiply (make 'np 'dp) 'x))]]
    (let [nx (numerator 'x)
          dx (denominator 'x)
          dxp (denominator-predecessor 'x)
          dc (succ 'dp)
          m (multiply-nat nx dx)
          scaled (multiply (make 'np 'dp) 'x)
          cross (to-cross 'x scaled 'bounded)
          packed-denominator (succ (combine 'dp dxp))
          a (multiply-nat nx packed-denominator)
          b (multiply-nat (multiply-nat 'np nx) dx)
          dc-m (multiply-nat dc m)
          np-m (multiply-nat 'np m)
          same-left
          (equality-transitive
           dc-m (multiply-nat nx (multiply-nat dc dx)) a
           (ring-equality dc-m (multiply-nat nx (multiply-nat dc dx)))
           (equality-congruent
            (function/lam [['candidate nat]] (multiply-nat nx 'candidate))
            (multiply-nat dc dx) packed-denominator
            (equality-symmetric
             packed-denominator (multiply-nat dc dx)
             (denominator-combine 'dp dxp))))
          shifted (rewrite-left dc-m a b same-left cross)
          bounded-cross
          (rewrite-right dc-m b np-m (ring-equality b np-m) shifted)
          not-positive
          (function/lam
           [['positive (below nat-zero nx)]]
           (let [dx-positive
                 (witness
                  (function/lam [['extra nat]]
                                (nat-equality (add-nat (succ nat-zero) 'extra)
                                              dx))
                  dxp (equality-reflexive dx))
                 m-positive
                 (strict-monotone dx nat-zero nx 'positive dx-positive)
                 below-proper
                 (use-witness
                  (function/lam [['extra nat]]
                                (nat-equality (add-nat 'np 'extra) 'dp))
                  (below 'np dc)
                  'proper
                  (function/lam
                   [['extra nat]
                    ['same (nat-equality (add-nat 'np 'extra) 'dp)]]
                   (witness
                    (function/lam [['gap nat]]
                                  (nat-equality (add-nat (succ 'np) 'gap) dc))
                    'extra
                    (equality-congruent
                     (function/lam [['candidate nat]] (succ 'candidate))
                     (add-nat 'np 'extra) 'dp 'same))))
                 strict (strict-monotone m 'np dc below-proper m-positive)
                 self-strict
                 (at-most-strict-transitive
                  dc-m np-m dc-m bounded-cross strict)]
             (function/app
              (function/const* 'nat/not-strictly-below-self [])
              dc-m self-strict)))
          numerator-zero
          (function/app
           (function/const* 'nat/equal-zero-of-not-positive [])
           nx not-positive)]
      (equality-congruent
       (function/lam [['candidate nat]]
                     (multiply-nat 'candidate (succ nat-zero)))
       nx nat-zero numerator-zero)))})

(def definition-specs [])
(def theorem-specs
  [at-most-multiply-left-cancel-spec
   multiply-divide-cancel-spec
   normalize-upper-spec
   normalize-lower-spec
   zero-of-proper-contraction-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-rate-null-prerequisites
  "The marker-guarded auxiliary chain `nnrat/zero-of-proper-contraction`
  elaborates against: the strict-below toolkit and the zero-of-not-positive
  case split, each entered only if its alias is absent. PUBLIC deliberately:
  nnrat-convex-normalized replays this module's theorem specs without the
  full extender (to sidestep the duplicate-identity conflict), so it must be
  able to install these prerequisites on their own."
  [checked-environment]
  (-> checked-environment
      (extend-spec-if-missing
       'nat/at-most-strict-below-transitive
       :bellman-scaled-fixed-point-uniqueness
       legacy-separation/at-most-strict-below-transitive-spec)
      (extend-spec-if-missing
       'nat/multiply-right-strict-monotone-positive
       :bellman-scaled-fixed-point-uniqueness
       legacy-separation/multiply-right-strict-monotone-positive-spec)
      (extend-spec-if-missing
       'nat/zero-not-successor
       :nat-infinite
       nat-infinite/zero-not-successor-spec)
      (extend-spec-if-missing
       'nat/positive-of-nonzero
       :nat-metric-separation
       nat-separation/positive-of-nonzero-spec)
      (extend-spec-if-missing
       'nat/equal-zero-of-not-positive
       :strict-contraction-uniqueness
       strict-uniqueness/equal-zero-of-not-positive-spec)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.identities])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-rate-null-prerequisites (support/extend-with :nnrat-order-scale (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.order-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
