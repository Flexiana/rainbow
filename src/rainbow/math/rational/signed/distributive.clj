(ns rainbow.math.rational.signed.distributive
  "Distributivity of signed multiplication over addition, and the scaled finite
  sum.

    signed/multiply-zero-left              0*a ~ 0
    signed/multiply-distributes-add-right  (a+b)*m ~ a*m + b*m
    signed/map-sum-scale-right             (sum f) * c ~ sum (f * c)

  Unfolded, the distributive law is an eight-monomial identity in six component
  atoms; the zero law is a three-monomial one with `nnrat/zero` as a further
  opaque atom.  Both are pure semiring identities, so each is a single
  `rainbow.math.rational.nnrat.ring` call.

  `signed/map-sum-scale-right` is the one proof with induction in it: the empty
  sum scales by the zero law and the cons step is distributivity against the
  induction hypothesis.  It is the pull-a-scalar-through-a-sum step of every
  dot-product rearrangement.

  Native and axiom-free; chains the signed multiplicative ring laws and the
  nnrat-ring tactic on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(def ^:private radd ring/radd)
(def ^:private rmul ring/rmul)
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- signed-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'signed/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- signed-dist-right [a b m]
  (app (function/const* 'signed/multiply-distributes-add-right []) a b m))

;; the two Grothendieck components of a signed product
(defn- product-positive [pl nl pr nr] (radd (rmul pl pr) (rmul nl nr)))
(defn- product-negative [pl nl pr nr] (radd (rmul pl nr) (rmul nl pr)))

;; 0*a has the two components (0*Pa + 0*Na) and (0*Na + 0*Pa), which differ only
;; by commuting, so the pair is equivalent to zero.
(def multiply-zero-left-spec
  {:name 'signed/multiply-zero-left :universes []
   :type (function/forall [['a signed]]
                          (seq-equiv (smul signed-zero 'a) signed-zero))
   :value
   (function/lam
    [['a signed]]
    (let [forward (product-positive nnrat-zero nnrat-zero (pos 'a) (neg 'a))
          backward (product-negative nnrat-zero nnrat-zero (pos 'a) (neg 'a))]
      (ring/equiv (radd forward nnrat-zero) (radd nnrat-zero backward))))})

(def multiply-distributes-add-right-spec
  {:name 'signed/multiply-distributes-add-right :universes []
   :type (function/forall
          [['a signed] ['b signed] ['m signed]]
          (seq-equiv (smul (sadd 'a 'b) 'm)
                     (sadd (smul 'a 'm) (smul 'b 'm))))
   :value
   (function/lam
    [['a signed] ['b signed] ['m signed]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b)
          Pm (pos 'm) Nm (neg 'm)
          ;; components of (a+b)*m
          sum-positive (product-positive (radd Pa Pb) (radd Na Nb) Pm Nm)
          sum-negative (product-negative (radd Pa Pb) (radd Na Nb) Pm Nm)
          ;; components of a*m + b*m
          split-positive (radd (product-positive Pa Na Pm Nm)
                               (product-positive Pb Nb Pm Nm))
          split-negative (radd (product-negative Pa Na Pm Nm)
                               (product-negative Pb Nb Pm Nm))]
      (ring/equiv (radd sum-positive split-negative)
                  (radd split-positive sum-negative))))})

(def map-sum-scale-right-spec
  {:name 'signed/map-sum-scale-right :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A signed)] ['c signed]
           ['xs (list-of 'A)]]
          (seq-equiv (smul (map-sum 'A 'f 'xs) 'c)
                     (map-sum 'A (function/lam [['i 'A]]
                                               (smul (app 'f 'i) 'c)) 'xs)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A signed)] ['c signed]
     ['xs (list-of 'A)]]
    (let [scaled (function/lam [['i 'A]] (smul (app 'f 'i) 'c))]
      (app (function/const* 'data/List.rec [data-level zero-level])
           'A
           (function/lam
            [['ys (list-of 'A)]]
            (seq-equiv (smul (map-sum 'A 'f 'ys) 'c) (map-sum 'A scaled 'ys)))
           ;; nil : 0 * c ~ 0
           (app (function/const* 'signed/multiply-zero-left []) 'c)
           (function/lam
            [['head 'A] ['tail (list-of 'A)]
             ['ih (seq-equiv (smul (map-sum 'A 'f 'tail) 'c)
                             (map-sum 'A scaled 'tail))]]
            (let [fh (app 'f 'head)
                  rest (map-sum 'A 'f 'tail)
                  start (smul (sadd fh rest) 'c)
                  middle (sadd (smul fh 'c) (smul rest 'c))
                  finish (sadd (smul fh 'c) (map-sum 'A scaled 'tail))]
              (signed-trans
               start middle finish
               (signed-dist-right fh rest 'c)
               (signed-add-respects (smul fh 'c) (smul fh 'c)
                                    (smul rest 'c) (map-sum 'A scaled 'tail)
                                    (signed-refl (smul fh 'c)) 'ih))))
           'xs)))})

(def definition-specs [])
(def theorem-specs
  [multiply-zero-left-spec
   multiply-distributes-add-right-spec
   map-sum-scale-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      signed-ring/extend-environment
      (support/extend-with :signed-distributive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
