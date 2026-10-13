(ns rainbow.math.rational.nnrat.lp-separable-multi-var
  "Zero total duality gap for a finite list of decoupled scalar nnrat LPs.

  The coefficients a, b, and c are functions on a shared index type.  Natural
  predecessor functions ap/adp and bp/bdp witness pointwise that a and b have
  the positive forms required by scalar strong duality.  The scalar zero-gap
  conjunct is transported along those witnesses and then lifted through the
  finite sum by map-sum-respects-equivalence.

  Universe-polymorphic in the index type, native, and axiom-free; chains the
  scalar strong-duality theorem and the finite-sum congruence on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.lp-strong-duality-general :as general]
            [rainbow.math.rational.nnrat.map-sum-respects :as respects]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- positive [numerator-predecessor denominator-predecessor]
  (make (succ numerator-predecessor) denominator-predecessor))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equal-nnrat [left right]
  (function/equality type-level nnrat left right))
(defn- app [f x]
  (function/app f x))
(defn- lam [name carrier body]
  (function/lam [[name carrier]] body))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-respects [A f g pointwise xs]
  (function/app
   (function/const* 'nnrat/map-sum-respects-equivalence [U])
   A f g pointwise xs))
(defn- substitute-nnrat [left right same predicate at-left]
  (function/app (function/const* 'equality/substitution [type-level])
                nnrat left right same predicate at-left))

(defn- primal-feasible [a b x]
  (at-most (multiply a x) b))
(defn- dual-feasible [a c y]
  (at-most c (multiply a y)))
(defn- gap [b c x y]
  (equivalent (multiply c x) (multiply b y)))
(defn- primal-optimal [a b c x]
  (function/forall
   [['x-alt nnrat] ['hp-alt (primal-feasible a b 'x-alt)]]
   (at-most (multiply c 'x-alt) (multiply c x))))
(defn- dual-optimal [a b c y]
  (function/forall
   [['y-alt nnrat] ['hd-alt (dual-feasible a c 'y-alt)]]
   (at-most (multiply b y) (multiply b 'y-alt))))

(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))
(def upper-family
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat list-nnrat))
(def layer
  (function/app (function/const* 'data/Product [type-level type-level])
                list-nnrat upper-family))
(defn- nil-of [carrier]
  (function/app (function/const* 'data/nil [type-level]) carrier))
(defn- cons-of [carrier head tail]
  (function/app (function/const* 'data/cons [type-level])
                carrier head tail))
(defn- matching-system [a b c x]
  (let [nil-nnrat (nil-of nnrat)
        nil-layer (nil-of layer)
        lower (divide c a)
        upper (divide (multiply c x) b)
        lowers (cons-of nnrat lower nil-nnrat)]
    (function/app
     (function/const* 'nnrat/farkas-elim-chain-solvable [])
     nil-layer lowers upper nil-nnrat)))
(defn- scalar-bundle [a b c x y]
  (proposition/conjunction
   (primal-feasible a b x)
   (proposition/conjunction
    (dual-feasible a c y)
    (proposition/conjunction
     (gap b c x y)
     (proposition/conjunction
      (primal-optimal a b c x)
      (proposition/conjunction
       (dual-optimal a b c y)
       (matching-system a b c x)))))))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))

(defn- scalar-gap [a b c x y bundle]
  (let [hp (primal-feasible a b x)
        hd (dual-feasible a c y)
        hgap (gap b c x y)
        primal-best (primal-optimal a b c x)
        dual-best (dual-optimal a b c y)
        system (matching-system a b c x)
        optimal-tail
        (proposition/conjunction
         primal-best (proposition/conjunction dual-best system))
        gap-tail (proposition/conjunction hgap optimal-tail)
        dual-tail (proposition/conjunction hd gap-tail)]
    (left-conjunct
     hgap optimal-tail
     (right-conjunct
      hd gap-tail
      (right-conjunct hp dual-tail bundle)))))

(def separable-multi-var-zero-gap-spec
  {:name 'nnrat/lp-separable-multi-var-zero-gap
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['a (function/arrow 'A nnrat)]
     ['b (function/arrow 'A nnrat)]
     ['c (function/arrow 'A nnrat)]
     ['ap (function/arrow 'A nat)]
     ['adp (function/arrow 'A nat)]
     ['bp (function/arrow 'A nat)]
     ['bdp (function/arrow 'A nat)]
     ['ha (function/forall
           [['i 'A]]
           (equal-nnrat
            (positive (app 'ap 'i) (app 'adp 'i))
            (app 'a 'i)))]
     ['hb (function/forall
           [['i 'A]]
           (equal-nnrat
            (positive (app 'bp 'i) (app 'bdp 'i))
            (app 'b 'i)))]
     ['idx (list-of 'A)]]
    (equivalent
     (map-sum
      'A
      (lam 'i 'A
           (multiply (app 'c 'i)
                     (divide (app 'b 'i) (app 'a 'i))))
      'idx)
     (map-sum
      'A
      (lam 'i 'A
           (multiply (app 'b 'i)
                     (divide (app 'c 'i) (app 'a 'i))))
      'idx)))
   :value
   (function/lam
    [['A type-u]
     ['a (function/arrow 'A nnrat)]
     ['b (function/arrow 'A nnrat)]
     ['c (function/arrow 'A nnrat)]
     ['ap (function/arrow 'A nat)]
     ['adp (function/arrow 'A nat)]
     ['bp (function/arrow 'A nat)]
     ['bdp (function/arrow 'A nat)]
     ['ha (function/forall
           [['i 'A]]
           (equal-nnrat
            (positive (app 'ap 'i) (app 'adp 'i))
            (app 'a 'i)))]
     ['hb (function/forall
           [['i 'A]]
           (equal-nnrat
            (positive (app 'bp 'i) (app 'bdp 'i))
            (app 'b 'i)))]
     ['idx (list-of 'A)]]
    (let [primal-map
          (lam 'i 'A
               (multiply (app 'c 'i)
                         (divide (app 'b 'i) (app 'a 'i))))
          dual-map
          (lam 'i 'A
               (multiply (app 'b 'i)
                         (divide (app 'c 'i) (app 'a 'i))))
          pointwise
          (lam
           'i 'A
           (let [ai (app 'a 'i)
                 bi (app 'b 'i)
                 ci (app 'c 'i)
                 api (app 'ap 'i)
                 adpi (app 'adp 'i)
                 bpi (app 'bp 'i)
                 bdpi (app 'bdp 'i)
                 positive-a (positive api adpi)
                 positive-b (positive bpi bdpi)
                 x (divide positive-b positive-a)
                 y (divide ci positive-a)
                 bundle
                 (function/app
                  (function/const*
                   'nnrat/lp-single-positive-constraint-strong-duality [])
                  api adpi bpi bdpi ci)
                 positive-gap
                 (scalar-gap positive-a positive-b ci x y bundle)
                 at-actual-a
                 (substitute-nnrat
                  positive-a ai (app 'ha 'i)
                  (lam 'a-value nnrat
                       (equivalent
                        (multiply ci (divide positive-b 'a-value))
                        (multiply positive-b (divide ci 'a-value))))
                  positive-gap)]
             (substitute-nnrat
              positive-b bi (app 'hb 'i)
              (lam 'b-value nnrat
                   (equivalent
                    (multiply ci (divide 'b-value ai))
                    (multiply 'b-value (divide ci ai))))
              at-actual-a)))]
      (map-sum-respects 'A primal-map dual-map pointwise 'idx)))})

(def definition-specs [])
(def theorem-specs [separable-multi-var-zero-gap-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.lp-strong-duality-general rainbow.math.rational.nnrat.map-sum-respects])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-lp-separable-multi-var (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.lp-separable-multi-var))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
