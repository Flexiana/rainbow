(ns rainbow.algorithms.proofs.interval-arithmetic
  "AHoF V40 Interval Arithmetic: the sound enclosure of a signed-rational value
  by a lower/upper bound pair, with the additive interval operation that
  underlies the reachability propagators (V40-V47). An interval is a pair
  [lo, hi] of signed rationals, and interval addition adds the bounds
  componentwise:

      [a, b] + [c, d] = [a + c, b + d]

  which is the sound enclosure of the sumset {x + y : x in [a,b], y in [c,d]}.
  Bounds are exact signed rationals (no floating rounding), so the enclosure is
  proved data. Addition reduces by reflexivity on concrete bounds; the
  containment/soundness predicate (x in [a,b] => lo <= x <= hi) uses the signed
  order and the width lo-hi lands on a non-canonical Grothendieck pair, so those
  stay executable/order-level concerns. What is proved here is the interval
  constructor with its projection laws and the componentwise additive law with
  worked instances.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 3 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.interval-arithmetic`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def interval
  (function/app (function/const* 'data/Product [type-level type-level])
                signed signed))

(defn- make-pair [lo hi]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed lo hi))
(defn- first-of [value]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed value))
(defn- second-of [value]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed value))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- make-interval [lo hi]
  (function/app (function/const* 'interval/make []) lo hi))
(defn- lower [value]
  (function/app (function/const* 'interval/lower []) value))
(defn- upper [value]
  (function/app (function/const* 'interval/upper []) value))
(defn- interval-add [left right]
  (function/app (function/const* 'interval/add []) left right))

;; Definitions --------------------------------------------------------------

(def make-spec
  {:name 'interval/make :kind :definition :universes []
   :type (function/arrow signed signed interval)
   :value (function/lam [['lo signed] ['hi signed]] (make-pair 'lo 'hi))})

(def lower-spec
  {:name 'interval/lower :kind :definition :universes []
   :type (function/arrow interval signed)
   :value (function/lam [['value interval]] (first-of 'value))})

(def upper-spec
  {:name 'interval/upper :kind :definition :universes []
   :type (function/arrow interval signed)
   :value (function/lam [['value interval]] (second-of 'value))})

;; [a,b] + [c,d] = [a+c, b+d]
(def add-spec
  {:name 'interval/add :kind :definition :universes []
   :type (function/arrow interval interval interval)
   :value (function/lam [['left interval] ['right interval]]
                        (make-pair (signed-add (first-of 'left)
                                               (first-of 'right))
                                   (signed-add (second-of 'left)
                                               (second-of 'right))))})

(def definition-specs [make-spec lower-spec upper-spec add-spec])

;; Theorems -----------------------------------------------------------------

;; Projection laws: the bounds read back what was stored.
(def lower-of-make-spec
  {:name 'interval/lower-of-make :universes []
   :type (function/forall [['lo signed] ['hi signed]]
                          (equality signed (lower (make-interval 'lo 'hi)) 'lo))
   :value (function/lam [['lo signed] ['hi signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (lower (make-interval 'lo 'hi))))})

(def upper-of-make-spec
  {:name 'interval/upper-of-make :universes []
   :type (function/forall [['lo signed] ['hi signed]]
                          (equality signed (upper (make-interval 'lo 'hi)) 'hi))
   :value (function/lam [['lo signed] ['hi signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (upper (make-interval 'lo 'hi))))})

;; The additive law: interval-add produces the componentwise-summed bounds.
(def add-bounds-spec
  {:name 'interval/add-bounds :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed] ['d signed]]
          (equality interval
                    (interval-add (make-interval 'a 'b) (make-interval 'c 'd))
                    (make-interval (signed-add 'a 'c) (signed-add 'b 'd))))
   :value (function/lam
           [['a signed] ['b signed] ['c signed] ['d signed]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            interval
            (interval-add (make-interval 'a 'b) (make-interval 'c 'd))))})

;; Worked additions ---------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make [])
                              (data-nat n) (data-nat 0))))

;; [1,3] + [2,4] = [3,7].
(def add-1-3-example-spec
  {:name 'interval/add-1-3-example :universes []
   :type (equality interval
                   (interval-add
                    (make-interval (signed-numeral 1) (signed-numeral 3))
                    (make-interval (signed-numeral 2) (signed-numeral 4)))
                   (make-interval (signed-numeral 3) (signed-numeral 7)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        interval
                        (interval-add
                         (make-interval (signed-numeral 1) (signed-numeral 3))
                         (make-interval (signed-numeral 2) (signed-numeral 4))))})

;; [0,2] + [0,3] = [0,5] (widths add: a 2-wide and a 3-wide enclosure sum to a
;; 5-wide one).
(def add-0-width-example-spec
  {:name 'interval/add-0-width-example :universes []
   :type (equality interval
                   (interval-add
                    (make-interval (signed-numeral 0) (signed-numeral 2))
                    (make-interval (signed-numeral 0) (signed-numeral 3)))
                   (make-interval (signed-numeral 0) (signed-numeral 5)))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        interval
                        (interval-add
                         (make-interval (signed-numeral 0) (signed-numeral 2))
                         (make-interval (signed-numeral 0) (signed-numeral 3))))})

(def theorem-specs
  [lower-of-make-spec upper-of-make-spec add-bounds-spec
   add-1-3-example-spec add-0-width-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :interval-arithmetic (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.interval-arithmetic))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
