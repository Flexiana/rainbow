(ns rainbow.math.finite.markov-geometric-decay
  "Geometric decay of total variation along kernel iterates.

  Brick 2 of the convergence half,
  built against the LANDED contraction inhabitant rather than an abstract
  premise: under normalized rows and a certified Dobrushin bound rho, the
  total variation between the n-th iterates of two equal-total-mass
  distributions is at most rho^n times the initial total variation. The
  induction step collapses one iterate through the total-variation
  congruence, applies the inhabitant at the iterated masses (equal total
  mass rides along by preservation), and folds the factor into the
  exact rational power. Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.markov-dobrushin-contraction :as contraction]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.power :as power]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def zero-level [:zero])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- mass-type [element] (function/arrow element nnrat))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- succ [value] (app (function/const* 'data/succ []) value))
(defn- rpow [base steps]
  (app (function/const* 'nnrat/power []) base steps))
(defn- total-mass [element states mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element states mass))
(defn- rows-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- coefficient [element states kernel]
  (app (function/const* 'markov/signed-kernel-dobrushin-coefficient [U])
       element states kernel))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- total-variation [element states left right]
  (app (function/const* 'markov/nnrat-total-variation [U])
       element states left right))
(defn- kernel-step [element states kernel mass]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass))
(defn- kernel-iterate [element states kernel steps mass]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [x y z pxy pyz]
  (app (function/const* 'nnrat/equivalent-transitive []) x y z pxy pyz))
(defn- order-respects [left eql right eqr same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left eql right eqr same-left same-right ordered))
(defn- order-reflexive [value]
  (app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- multiply-monotone [factor a b ordered]
  (app (function/const* 'nnrat/multiply-monotone []) factor a b ordered))
(defn- multiply-one-left [value]
  (app (function/const* 'nnrat/multiply-one-left []) value))
(defn- multiply-associative [a b c]
  (app (function/const* 'nnrat/multiply-associative []) a b c))

(def iterate-total-variation-decay-spec
  "TV(iterate n left, iterate n right) <= power rho n * TV(left, right)."
  {:name 'markov/nnrat-kernel-iterate-total-variation-decay
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['rho nnrat]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel) (from-nnrat 'rho))]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['equal-total-mass (req (total-mass 'S 'states 'left)
                             (total-mass 'S 'states 'right))]
     ['steps nat]]
    (rle (total-variation 'S 'states
                          (kernel-iterate 'S 'states 'kernel 'steps 'left)
                          (kernel-iterate 'S 'states 'kernel 'steps 'right))
         (rmul (rpow 'rho 'steps)
               (total-variation 'S 'states 'left 'right))))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['rho nnrat]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel) (from-nnrat 'rho))]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['equal-total-mass (req (total-mass 'S 'states 'left)
                             (total-mass 'S 'states 'right))]]
    (let [tv0 (total-variation 'S 'states 'left 'right)
          iterate-of (fn [n mass] (kernel-iterate 'S 'states 'kernel n mass))
          tv-at (fn [n] (total-variation 'S 'states
                                         (iterate-of n 'left)
                                         (iterate-of n 'right)))
          preserved (fn [mass]
                      (app (function/const*
                            'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence
                            [U])
                           'S 'states 'kernel mass 'normalized 'n))
          motive
          (function/lam
           [['n nat]]
           (rle (total-variation 'S 'states
                                 (kernel-iterate 'S 'states 'kernel 'n 'left)
                                 (kernel-iterate 'S 'states 'kernel 'n 'right))
                (rmul (rpow 'rho 'n) tv0)))
          base
          (order-respects
           tv0 tv0 (rmul (rpow 'rho (function/const* 'data/zero [])) tv0) tv0
           (equivalent-reflexive tv0)
           (multiply-one-left tv0)
           (order-reflexive tv0))
          step
          (function/lam
           [['n nat] ['previous (app motive 'n)]]
           (let [it-l (iterate-of 'n 'left)
                 it-r (iterate-of 'n 'right)
                 tv-n (tv-at 'n)
                 tv-s (tv-at (succ 'n))
                 step-l (kernel-step 'S 'states 'kernel it-l)
                 step-r (kernel-step 'S 'states 'kernel it-r)
                 pow-n (rpow 'rho 'n)
                 envelope-n (rmul pow-n tv0)
                 collapse
                 (app (function/const*
                       'markov/nnrat-total-variation-respects-pointwise-equivalent
                       [U])
                      'S 'states
                      (iterate-of (succ 'n) 'left) step-l
                      (iterate-of (succ 'n) 'right) step-r
                      (function/lam
                       [['target 'S]]
                       (app (function/const*
                             'markov/nnrat-kernel-iterate-successor [U])
                            'S 'states 'kernel 'n 'left 'target))
                      (function/lam
                       [['target 'S]]
                       (app (function/const*
                             'markov/nnrat-kernel-iterate-successor [U])
                            'S 'states 'kernel 'n 'right 'target)))
                 equal-total-n
                 (equivalent-transitive
                  (total-mass 'S 'states it-l)
                  (total-mass 'S 'states 'left)
                  (total-mass 'S 'states it-r)
                  (preserved 'left)
                  (equivalent-transitive
                   (total-mass 'S 'states 'left)
                   (total-mass 'S 'states 'right)
                   (total-mass 'S 'states it-r)
                   'equal-total-mass
                   (equivalent-symmetric
                    (total-mass 'S 'states it-r)
                    (total-mass 'S 'states 'right)
                    (preserved 'right))))
                 contracts
                 (app (function/const* 'markov/nnrat-dobrushin-contraction [U])
                      'S 'states 'kernel 'rho
                      'normalized 'coefficient-bound
                      it-l it-r equal-total-n)
                 one-step
                 (order-respects
                  tv-s (total-variation 'S 'states step-l step-r)
                  (rmul 'rho tv-n) (rmul 'rho tv-n)
                  collapse
                  (equivalent-reflexive (rmul 'rho tv-n))
                  contracts)
                 pushed
                 (order-transitive
                  tv-s (rmul 'rho tv-n) (rmul 'rho envelope-n)
                  one-step
                  (multiply-monotone 'rho tv-n envelope-n 'previous))]
             (order-respects
              tv-s tv-s
              (rmul (rmul 'rho pow-n) tv0)
              (rmul 'rho envelope-n)
              (equivalent-reflexive tv-s)
              (multiply-associative 'rho pow-n tv0)
              pushed)))]
      (function/lam
       [['steps nat]]
       (app (function/const* 'data/Nat.rec [zero-level])
            motive base step 'steps))))})

(def definition-specs [])
(def theorem-specs [iterate-total-variation-decay-spec])

(defn- extend-if-missing [env marker extend]
  (if (environment/resolve-id env marker) env (extend env)))

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      contraction/extend-environment
      (extend-spec-if-missing
       'markov/nnrat-kernel-iterate
       :finite-markov-iteration iteration/kernel-iterate-spec)
      (extend-spec-if-missing
       'markov/nnrat-kernel-iterate-successor
       :finite-markov-iteration iteration/kernel-iterate-successor-spec)
      (extend-spec-if-missing
       'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence
       :finite-markov-iteration iteration/kernel-iterate-preserves-total-mass-spec)
      (extend-if-missing 'nnrat/power power/extend-environment)
      (extend-spec-if-missing
       'nnrat/multiply-associative
       :nnrat-product-reassociation reassociation/multiply-associative-spec)
      (support/extend-with :finite-markov-geometric-decay theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
