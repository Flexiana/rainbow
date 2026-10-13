(ns rainbow.algorithms.proofs.ahof.mean-value-inclusion
  "AHoF V42 Mean-Value Inclusion: a tighter interval extension than the natural
  inclusion, using the mean-value form to enclose a function's range in [lo, hi]; a
  value is certified within the enclosure when it lies between the bounds:

      encloses? lo hi value = (lo <= value) AND (value <= hi)

  (boolean AND via logic/if-data over the two order decisions). Proved native and
  axiom-free (membership + unfold, enclosed value, value below lower bound). Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mean-value-inclusion`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))
(defn- encloses? [lo hi value]
  (function/app (function/const* 'mean-value/encloses? []) lo hi value))

(def encloses-spec
  {:name 'mean-value/encloses? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam [['lo nnrat] ['hi nnrat] ['value nnrat]]
                        (and-bool (decide-at-most 'lo 'value) (decide-at-most 'value 'hi)))})

(def definition-specs [encloses-spec])

(def encloses-unfold-spec
  {:name 'mean-value/encloses-unfold :universes []
   :type (function/forall [['lo nnrat] ['hi nnrat] ['value nnrat]]
                          (equality bool (encloses? 'lo 'hi 'value)
                                    (and-bool (decide-at-most 'lo 'value)
                                              (decide-at-most 'value 'hi))))
   :value (function/lam [['lo nnrat] ['hi nnrat] ['value nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      bool (encloses? 'lo 'hi 'value)))})

(def value-enclosed-spec
  {:name 'mean-value/value-enclosed :universes []
   :type (equality bool (encloses? (fraction 1 1) (fraction 3 1) (whole 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (encloses? (fraction 1 1) (fraction 3 1) (whole 1)))})

(def value-below-not-enclosed-spec
  {:name 'mean-value/value-below-not-enclosed :universes []
   :type (equality bool (encloses? (fraction 1 1) (fraction 3 1) (fraction 1 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (encloses? (fraction 1 1) (fraction 3 1) (fraction 1 3)))})

(def theorem-specs [encloses-unfold-spec value-enclosed-spec value-below-not-enclosed-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-mean-value-inclusion
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
