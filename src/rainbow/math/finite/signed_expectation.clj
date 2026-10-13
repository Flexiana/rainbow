(ns rainbow.math.finite.signed-expectation
  "Normalized finite expectation for exact signed-rational outcomes.

  Transition weights are signed rationals with explicit nonnegativity and
  normalization premises.  The expectation is a finite weighted sum over a
  finset enumeration.  It is monotone, adding a constant exposes total mass,
  and normalized expectation preserves pointwise additive epsilon bounds.

  This is reusable stochastic proof infrastructure for signed rewards and
  costs.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]
            [rainbow.math.rational.signed.map-sum-algebra :as sum-algebra]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'signed/map-sum [U]) element mapping items))
(defn- total-mass [element source mass]
  (app (function/const* 'probability/signed-total-mass [U])
       element source mass))
(defn- expectation [element source mass value]
  (app (function/const* 'probability/signed-expectation [U])
       element source mass value))
(defn- equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equiv-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- equiv-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- add-respects [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime first second))
(defn- multiply-respects [left left-prime right right-prime first second]
  (app (function/const* 'signed/multiply-respects-equivalence [])
       left left-prime right right-prime first second))

(def total-mass-spec
  {:name 'probability/signed-total-mass
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]]
    (function/arrow (function/arrow 'A signed) signed))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]]
    (map-sum 'A 'mass (enumeration 'A 'source)))})

(def expectation-spec
  {:name 'probability/signed-expectation
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]]
    (function/arrow (function/arrow 'A signed) signed))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['value (function/arrow 'A signed)]]
    (map-sum
     'A
     (function/lam
      [['item 'A]] (multiply (app 'mass 'item) (app 'value 'item)))
     (enumeration 'A 'source)))})

(def expectation-monotone-spec
  {:name 'probability/signed-expectation-monotone
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['lower-value (function/arrow 'A signed)]
     ['upper-value (function/arrow 'A signed)]
     ['mass-nonnegative
      (function/forall
       [['item 'A]] (at-most signed-zero (app 'mass 'item)))]
     ['pointwise
      (function/forall
       [['item 'A]]
       (at-most (app 'lower-value 'item) (app 'upper-value 'item)))]]
    (at-most (expectation 'A 'source 'mass 'lower-value)
             (expectation 'A 'source 'mass 'upper-value)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['lower-value (function/arrow 'A signed)]
     ['upper-value (function/arrow 'A signed)]
     ['mass-nonnegative
      (function/forall
       [['item 'A]] (at-most signed-zero (app 'mass 'item)))]
     ['pointwise
      (function/forall
       [['item 'A]]
       (at-most (app 'lower-value 'item) (app 'upper-value 'item)))]]
    (app
     (function/const* 'signed/weighted-sum-monotone [U])
     'A 'mass 'lower-value 'upper-value
     'mass-nonnegative 'pointwise (enumeration 'A 'source)))})

(def expectation-add-constant-spec
  {:name 'probability/signed-expectation-add-constant
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['value (function/arrow 'A signed)] ['epsilon signed]]
    (equivalent
     (expectation
      'A 'source 'mass
      (function/lam
       [['item 'A]] (add (app 'value 'item) 'epsilon)))
     (add (expectation 'A 'source 'mass 'value)
          (multiply (total-mass 'A 'source 'mass) 'epsilon))))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['value (function/arrow 'A signed)] ['epsilon signed]]
    (let [items (enumeration 'A 'source)
          shifted-products
          (function/lam
           [['item 'A]]
           (multiply (app 'mass 'item)
                     (add (app 'value 'item) 'epsilon)))
          split-products
          (function/lam
           [['item 'A]]
           (add (multiply (app 'mass 'item) (app 'value 'item))
                (multiply (app 'mass 'item) 'epsilon)))
          value-products
          (function/lam
           [['item 'A]]
           (multiply (app 'mass 'item) (app 'value 'item)))
          epsilon-products
          (function/lam
           [['item 'A]] (multiply (app 'mass 'item) 'epsilon))
          shifted-sum (map-sum 'A shifted-products items)
          split-sum (map-sum 'A split-products items)
          value-sum (map-sum 'A value-products items)
          epsilon-sum (map-sum 'A epsilon-products items)
          total (total-mass 'A 'source 'mass)
          split-pointwise
          (function/lam
           [['item 'A]]
           (app
            (function/const* 'signed/multiply-distributes-add-left [])
            (app 'mass 'item) (app 'value 'item) 'epsilon))
          expose-split
          (app
           (function/const* 'signed/map-sum-respects-equivalence [U])
           'A shifted-products split-products split-pointwise items)
          split-sums
          (app (function/const* 'signed/map-sum-add [U])
               'A value-products epsilon-products items)
          scale-out
          (app (function/const* 'signed/map-sum-scale-right [U])
               'A 'mass 'epsilon items)
          collect-scale
          (add-respects
           value-sum value-sum epsilon-sum (multiply total 'epsilon)
           (equiv-reflexive value-sum)
           (equiv-symmetric
            (multiply total 'epsilon) epsilon-sum scale-out))]
      (equiv-transitive
       shifted-sum split-sum
       (add value-sum (multiply total 'epsilon))
       expose-split
       (equiv-transitive
        split-sum (add value-sum epsilon-sum)
        (add value-sum (multiply total 'epsilon))
        split-sums collect-scale))))})

(def expectation-additive-upper-bound-normalized-spec
  {:name 'probability/signed-expectation-additive-upper-bound-normalized
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['mass-nonnegative
      (function/forall
       [['item 'A]] (at-most signed-zero (app 'mass 'item)))]
     ['normalized
      (equivalent (total-mass 'A 'source 'mass) signed-one)]
     ['lower-value (function/arrow 'A signed)]
     ['upper-value (function/arrow 'A signed)]
     ['epsilon signed]
     ['pointwise
      (function/forall
       [['item 'A]]
       (at-most (app 'lower-value 'item)
                (add (app 'upper-value 'item) 'epsilon)))]]
    (at-most (expectation 'A 'source 'mass 'lower-value)
             (add (expectation 'A 'source 'mass 'upper-value) 'epsilon)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A signed)]
     ['mass-nonnegative
      (function/forall
       [['item 'A]] (at-most signed-zero (app 'mass 'item)))]
     ['normalized
      (equivalent (total-mass 'A 'source 'mass) signed-one)]
     ['lower-value (function/arrow 'A signed)]
     ['upper-value (function/arrow 'A signed)]
     ['epsilon signed]
     ['pointwise
      (function/forall
       [['item 'A]]
       (at-most (app 'lower-value 'item)
                (add (app 'upper-value 'item) 'epsilon)))]]
    (let [shifted-value
          (function/lam
           [['item 'A]] (add (app 'upper-value 'item) 'epsilon))
          lower-expectation
          (expectation 'A 'source 'mass 'lower-value)
          shifted-expectation
          (expectation 'A 'source 'mass shifted-value)
          upper-expectation
          (expectation 'A 'source 'mass 'upper-value)
          total (total-mass 'A 'source 'mass)
          target (add upper-expectation 'epsilon)
          expectation-ordered
          (app
           (function/const* 'probability/signed-expectation-monotone [U])
           'A 'source 'mass 'lower-value shifted-value
           'mass-nonnegative 'pointwise)
          affine
          (app
           (function/const* 'probability/signed-expectation-add-constant [U])
           'A 'source 'mass 'upper-value 'epsilon)
          normalize-product
          (multiply-respects
           total signed-one 'epsilon 'epsilon
           'normalized (equiv-reflexive 'epsilon))
          one-product
          (app (function/const* 'signed/multiply-one-left []) 'epsilon)
          normalized-product
          (equiv-transitive
           (multiply total 'epsilon)
           (multiply signed-one 'epsilon) 'epsilon
           normalize-product one-product)
          normalize-affine
          (add-respects
           upper-expectation upper-expectation
           (multiply total 'epsilon) 'epsilon
           (equiv-reflexive upper-expectation) normalized-product)
          shifted-is-target
          (equiv-transitive
           shifted-expectation
           (add upper-expectation (multiply total 'epsilon))
           target affine normalize-affine)
          shifted-at-most-target
          (app (function/const* 'signed/equivalent-to-at-most [])
               shifted-expectation target shifted-is-target)]
      (app
       (function/const* 'signed/at-most-transitive [])
       lower-expectation shifted-expectation target
       expectation-ordered shifted-at-most-target)))})

(def definition-specs [total-mass-spec expectation-spec])
(def theorem-specs
  [expectation-monotone-spec
   expectation-add-constant-spec
   expectation-additive-upper-bound-normalized-spec])

(defn- extend-spec-if-missing [env alias producer spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env producer [spec])))

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.map-sum-algebra])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :signed-multiply-ring multiply-ring/theorem-specs) (extend-specs-if-missing :signed-distributive distributive/theorem-specs) (extend-spec-if-missing 'signed/multiply-distributes-add-left :finite-matrix-action-scale action-scale/multiply-distributes-add-left-spec) (extend-spec-if-missing 'signed/equivalent-symmetric :signed-equivalence-laws equivalence-laws/equivalent-symmetric-spec) (support/extend-with :finite-signed-expectation (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.signed-expectation))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
