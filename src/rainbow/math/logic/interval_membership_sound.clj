(ns rainbow.math.logic.interval-membership-sound
  "Universal soundness of the two-clause interval/box membership test, composing the
  general boolean-AND soundness (rainbow.math.logic.boolean-and) with the decidable order:

      contains? lo hi x = and (decide (lo <= x)) (decide (x <= hi))

  Proved for ALL lo, hi, x:
    contains-sound : contains? lo hi x = true -> (lo <= x) AND (x <= hi)

  So whenever the membership test accepts a point, the point provably satisfies both
  interval bounds -- the universal guarantee behind the AHoF interval/reachability/box
  membership rows (V40, V41, V33, V34, V59, ...), which the catalog only exercised on
  worked instances. Native and axiom-free; chains rainbow.math.logic.boolean-and."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))

(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- and-op [a b] (function/app (function/const* 'boolean/and []) a b))
(defn- conjunction [l r]
  (function/app (function/const* 'proposition/conjunction []) l r))
(defn- contains? [lo hi x]
  (function/app (function/const* 'ims/contains? []) lo hi x))

;; contains? lo hi x = and (decide lo<=x) (decide x<=hi)
(def contains-spec
  {:name 'ims/contains? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam [['lo nnrat] ['hi nnrat] ['x nnrat]]
                        (and-op (decide-at-most 'lo 'x) (decide-at-most 'x 'hi)))})

(def definition-specs [contains-spec])

;; contains? lo hi x = true -> (lo <= x) AND (x <= hi)
(def contains-sound-spec
  {:name 'ims/contains-sound :universes []
   :type (function/forall
          [['lo nnrat] ['hi nnrat] ['x nnrat]]
          (function/arrow (eq-bool (contains? 'lo 'hi 'x) true-value)
                          (conjunction (at-most 'lo 'x) (at-most 'x 'hi))))
   :value (function/lam
           [['lo nnrat] ['hi nnrat] ['x nnrat]
            ['h (eq-bool (contains? 'lo 'hi 'x) true-value)]]
           (let [dl (decide-at-most 'lo 'x)
                 dr (decide-at-most 'x 'hi)
                 left-true (function/app (function/const* 'boolean/and-implies-left [])
                                         dl dr 'h)
                 right-true (function/app (function/const* 'boolean/and-implies-right [])
                                          dl dr 'h)]
             (function/app
              (function/const* 'proposition/conjoin [])
              (at-most 'lo 'x) (at-most 'x 'hi)
              (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                            'lo 'x left-true)
              (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                            'x 'hi right-true))))})

(def theorem-specs [contains-sound-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :interval-membership-sound
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
