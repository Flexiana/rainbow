(ns rainbow.math.linear.vector.equivalence
  "Componentwise equivalence of signed-rational vectors: two vectors are
  equivalent when every pair of components is signed-equivalent. This is a
  conjunction folded over the two component lists (a Prop-valued nested
  data/List.rec, the shape of vector/add but eliminating into Prop):

      equivalent [a..] [b..]  =  (a_1 ~ b_1) AND ... AND (a_n ~ b_n) AND True

  It is the vector analogue of signed/equivalent, and it is what lets worked
  vector results that come out as non-canonical Grothendieck pairs (e.g. a
  subtraction [4,4]-[1,1] whose components are the pair (4,1), not the reduced 3)
  be proven equal to their reduced vectors -- unblocking direct-search and
  non-origin optimizer worked examples.

  Requires the finite-vector capability (data/List over signed) in the
  environment."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))
(def prop 'Prop)

(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r le re]
  (function/app (function/const* 'proposition/conjoin []) l r le re))
(defn- negation [x]
  (function/app (function/const* 'proposition/negation []) x))
(def truth (function/const* 'proposition/truth []))
(def falsity (function/const* 'proposition/falsity []))
(def trivial (function/const* 'proposition/trivial []))
(defn- equivalent-reflexive [v]
  (function/app (function/const* 'signed/equivalent-reflexive []) v))

(defn- nil-vector []
  (function/app (function/const* 'data/nil [type-level]) signed))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- signed-make [p n]
  (function/app (function/const* 'signed/make []) p n))
(defn- nnrat-num [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-subtract [l r]
  (function/app (function/const* 'signed/subtract []) l r))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (nil-vector) (reverse components)))

(defn- vec-equivalent [u v]
  (function/app (function/const* 'vector/equivalent []) u v))

(def nat (function/const* 'data/Nat []))
(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))

;; A proof of `signed/equivalent left right` by reflexivity on the reduced nat
;; cross-product (positive(left)+negative(right) vs positive(right)+negative(left)).
(defn- signed-cross [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; Definitions --------------------------------------------------------------

;; Nested List.rec producing a Prop: conjunction of componentwise equivalences.
(def equivalent-spec
  {:name 'vector/equivalent :kind :definition :universes []
   :type (function/arrow vector-type vector-type prop)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (function/app
     (function/app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam [['ignored vector-type]] (function/arrow vector-type prop))
      ;; left is nil: equivalent iff the other vector is also nil.
      (function/lam
       [['other vector-type]]
       (function/app
        (function/const* 'data/List.rec [type-level type-level])
        signed
        (function/lam [['ignored vector-type]] prop)
        truth                                ; nil/nil -> equivalent (True)
        (function/lam [['other-head signed] ['other-tail vector-type]
                       ['ignored-recur prop]]
                      falsity)               ; nil/cons -> not equivalent
        'other))
      (function/lam
       [['head signed] ['tail vector-type]
        ['recur (function/arrow vector-type prop)]]
       (function/lam
        [['other vector-type]]
        (function/app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam [['ignored vector-type]] prop)
         falsity                              ; cons/nil -> not equivalent
         (function/lam
          [['other-head signed] ['other-tail vector-type]
           ['ignored-recur prop]]
          (conjunction (signed-equivalent 'head 'other-head)
                       (function/app 'recur 'other-tail)))
         'other)))
      'left)
     'right))})

(def definition-specs [equivalent-spec])

;; Theorems -----------------------------------------------------------------

;; The empty vectors are equivalent (the empty conjunction is True).
(def nil-equivalent-spec
  {:name 'vector/nil-equivalent :universes []
   :type (vec-equivalent (nil-vector) (nil-vector))
   :value trivial})

;; A reflexive two-dimensional equivalence: [1,2] ~ [1,2].
(def reflexive-example-spec
  (let [s1 (signed-numeral 1) s2 (signed-numeral 2)]
    {:name 'vector/reflexive-example :universes []
     :type (vec-equivalent (make-vector s1 s2) (make-vector s1 s2))
     :value (conjoin (signed-equivalent s1 s1)
                     (conjunction (signed-equivalent s2 s2) truth)
                     (equivalent-reflexive s1)
                     (conjoin (signed-equivalent s2 s2) truth
                              (equivalent-reflexive s2) trivial))}))

;; The value-demonstrating case: a subtraction whose components come out as the
;; non-canonical pair (4,1) is proven equivalent to the reduced vector [3,3].
(def subtract-equivalent-example-spec
  (let [four (signed-numeral 4) one (signed-numeral 1) three (signed-numeral 3)
        diff (signed-subtract four one)]           ; reduces to the pair (4,1)
    {:name 'vector/subtract-equivalent-example :universes []
     :type (vec-equivalent (make-vector diff diff) (make-vector three three))
     :value (conjoin (signed-equivalent diff three)
                     (conjunction (signed-equivalent diff three) truth)
                     (signed-cross diff three)
                     (conjoin (signed-equivalent diff three) truth
                              (signed-cross diff three) trivial))}))

;; Negative shape checks (kernel-checked): unequal-length vectors are NOT
;; equivalent. Since the mismatched case reduces to False, the negation is proven
;; by the identity `lambda h. h` (which typechecks as claim -> False because the
;; claim is definitionally False).
(def nil-cons-not-equivalent-spec
  (let [claim (vec-equivalent (nil-vector) (make-vector (signed-numeral 1)))]
    {:name 'vector/nil-cons-not-equivalent :universes []
     :type (negation claim)
     :value (function/lam [['contra claim]] 'contra)}))

(def cons-nil-not-equivalent-spec
  (let [claim (vec-equivalent (make-vector (signed-numeral 1)) (nil-vector))]
    {:name 'vector/cons-nil-not-equivalent :universes []
     :type (negation claim)
     :value (function/lam [['contra claim]] 'contra)}))

(def theorem-specs
  [nil-equivalent-spec reflexive-example-spec
   subtract-equivalent-example-spec nil-cons-not-equivalent-spec
   cons-nil-not-equivalent-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :vector-equivalence
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
