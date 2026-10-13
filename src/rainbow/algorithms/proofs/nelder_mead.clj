(ns rainbow.algorithms.proofs.nelder-mead
  "AHoF O36 Nelder-Mead Simplex: the reflection move, the workhorse simplex
  transform. The worst vertex is reflected through the centroid of the remaining
  vertices:

      reflected = centroid + (centroid - worst)

  a finite-vector subtract and add (unit reflection coefficient). Because the
  reflection subtracts a non-origin vertex, its components come out as
  non-canonical Grothendieck pairs, so the worked result is proven with the
  componentwise vector equivalence (vector/equivalent) rather than pair equality
  -- the first optimizer worked example away from the origin. The expand,
  contract, and shrink moves and the centroid computation stay in the executable
  reference.

  Requires the finite-vector and vector-equivalence capabilities.

  Scope (measured by the kernel): this module has 1 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.nelder-mead`
  prints this classification."
  (:require [rainbow.math.linear.vector.equivalence :as dep-vector-equivalence]
            [rainbow.math.finite.vector :as dep-finite-vector]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [type-level]) signed))

(defn- vector-add [l r] (function/app (function/const* 'vector/add []) l r))
(defn- vector-subtract [l r]
  (function/app (function/const* 'vector/subtract []) l r))
(defn- vec-equivalent [u v]
  (function/app (function/const* 'vector/equivalent []) u v))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r le re]
  (function/app (function/const* 'proposition/conjoin []) l r le re))
(def truth (function/const* 'proposition/truth []))
(def trivial (function/const* 'proposition/trivial []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))
(defn- signed-subtract [l r]
  (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-add [l r] (function/app (function/const* 'signed/add []) l r))
(defn- make-vector [& components]
  (reduce (fn [tail component]
            (function/app (function/const* 'data/cons [type-level])
                          signed component tail))
          (function/app (function/const* 'data/nil [type-level]) signed)
          (reverse components)))

(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- signed-cross [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

(defn- reflect [centroid worst]
  (function/app (function/const* 'nelder/reflect []) centroid worst))

;; Definitions --------------------------------------------------------------

;; reflected = centroid + (centroid - worst)
(def reflect-spec
  {:name 'nelder/reflect :kind :definition :universes []
   :type (function/arrow vector-type vector-type vector-type)
   :value (function/lam [['centroid vector-type] ['worst vector-type]]
                        (vector-add 'centroid
                                    (vector-subtract 'centroid 'worst)))})

(def definition-specs [reflect-spec])

;; Theorems -----------------------------------------------------------------

(def reflect-unfold-spec
  {:name 'nelder/reflect-unfold :universes []
   :type (function/forall
          [['centroid vector-type] ['worst vector-type]]
          (equality vector-type (reflect 'centroid 'worst)
                    (vector-add 'centroid
                                (vector-subtract 'centroid 'worst))))
   :value (function/lam [['centroid vector-type] ['worst vector-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         vector-type (reflect 'centroid 'worst)))})

;; Reflecting the worst vertex [1,1] through the centroid [2,2] gives [3,3].
;; Each reflected component is centroid + (centroid - worst) = 2 + (2 - 1),
;; which reduces to the Grothendieck pair (4,1) ~ 3, so the result is proven
;; equivalent (not equal) to the reduced [3,3].
(def reflect-example-spec
  (let [c (signed-numeral 2) w (signed-numeral 1) three (signed-numeral 3)
        component (signed-add c (signed-subtract c w))]  ; reduces to (4,1)
    {:name 'nelder/reflect-example :universes []
     :type (vec-equivalent
            (reflect (make-vector c c) (make-vector w w))
            (make-vector three three))
     :value (conjoin (signed-equivalent component three)
                     (conjunction (signed-equivalent component three) truth)
                     (signed-cross component three)
                     (conjoin (signed-equivalent component three) truth
                              (signed-cross component three) trivial))}))

(def theorem-specs [reflect-unfold-spec reflect-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-finite-vector/extend-environment (dep-vector-equivalence/extend-environment checked-environment)) :nelder-mead
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
