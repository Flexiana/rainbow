(ns rainbow.math.rational.nnrat.quadratic-zero
  "Zero reflection and the equality case of the nnrat square inequality.

    nat/multiply-self-zero
    nnrat/square-zero-reflects
    nnrat/quadratic-equality-reflects

  The quadratic theorem proves

      p*p + n*n ~ p*n + n*p  ->  p ~ n.

  Decidable total order chooses the smaller component.  Difference existence
  writes the larger as smaller+gap; verified ring normalization reduces the
  hypothesis to core+gap^2 ~ core, additive cancellation forces gap^2~0, and
  square-zero reflection forces gap~0.  Native and axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancel-zero :as add-cancel]
            [rainbow.math.rational.nnrat.add-zero-split :as zero-split]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.order-difference :as difference]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def zero-nat (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- eq-nat [left right]
  (function/equality type-level nat left right))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- rnum [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rat-at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- decide-at-most [left right]
  (app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- nat-transitive [left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       nat left middle right first second))
(defn- nat-symmetric [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       nat left right same))
(defn- nat-reflexive [value]
  (app (function/const* 'equality/reflexive [type-level]) nat value))
(defn- rat-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- rat-add-respects [left left-prime right right-prime
                          left-same right-same]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- rat-multiply-respects [left left-prime right right-prime
                               left-same right-same]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- difference-predicate [lower upper]
  (function/lam
   [['gap nnrat]]
   (rat-equivalent (radd lower 'gap) upper)))
(defn- existence [predicate]
  (app (function/const* 'proposition/existence [type-level])
       nnrat predicate))
(defn- use-witness [predicate goal exists handler]
  (app (function/const* 'proposition/use-witness [type-level])
       nnrat predicate goal exists handler))
(defn- quadratic-left [first second]
  (radd (rmul first first) (rmul second second)))
(defn- quadratic-right [first second]
  (radd (rmul first second) (rmul second first)))

(def multiply-self-zero-spec
  {:name 'nat/multiply-self-zero :universes []
   :type
   (function/forall
    [['value nat]
     ['zero-product (eq-nat (nmul 'value 'value) zero-nat)]]
    (eq-nat 'value zero-nat))
   :value
   (function/lam
    [['value nat]]
    (app
     (function/const* 'data/Nat.rec [zero-level])
     (function/lam
      [['current nat]]
      (function/arrow
       (eq-nat (nmul 'current 'current) zero-nat)
       (eq-nat 'current zero-nat)))
     (function/lam
      [['zero-product (eq-nat (nmul zero-nat zero-nat) zero-nat)]]
      (nat-reflexive zero-nat))
     (function/lam
      [['previous nat]
       ['ignored
        (function/arrow
         (eq-nat (nmul 'previous 'previous) zero-nat)
         (eq-nat 'previous zero-nat))]]
      (function/lam
       [['zero-product
         (eq-nat (nmul (succ 'previous) (succ 'previous)) zero-nat)]]
       (app (function/const* 'nat/multiply-succ-zero-left [])
            (succ 'previous) 'previous 'zero-product)))
     'value))})

(def square-zero-reflects-spec
  {:name 'nnrat/square-zero-reflects :universes []
   :type
   (function/forall
    [['value nnrat]
     ['zero-square
      (rat-equivalent (rmul 'value 'value) nnrat-zero)]]
    (rat-equivalent 'value nnrat-zero))
   :value
   (function/lam
    [['value nnrat]
     ['zero-square
      (rat-equivalent (rmul 'value 'value) nnrat-zero)]]
    (let [numerator (rnum 'value)
          numerator-square (nmul numerator numerator)
          square-zero
          (nat-transitive
           numerator-square (nmul numerator-square (succ zero-nat)) zero-nat
           (nat-symmetric
            (nmul numerator-square (succ zero-nat)) numerator-square
            (app (function/const* 'nat/multiply-one-right [])
                 numerator-square))
           'zero-square)
          numerator-zero
          (app (function/const* 'nat/multiply-self-zero [])
               numerator square-zero)]
      (nat-transitive
       (nmul numerator (succ zero-nat)) numerator zero-nat
       (app (function/const* 'nat/multiply-one-right []) numerator)
       numerator-zero)))})

(defn- ordered-quadratic-reflect
  [lower upper ordered equation]
  (let [goal (rat-equivalent upper lower)
        predicate (difference-predicate lower upper)]
    (use-witness
     predicate goal
     (app (function/const* 'nnrat/at-most-difference [])
          lower upper ordered)
     (function/lam
      [['gap nnrat]
       ['gap-witness (rat-equivalent (radd lower 'gap) upper)]]
      (let [sum (radd lower 'gap)
            upper-to-sum (rat-symmetric sum upper 'gap-witness)
            original-left (quadratic-left upper lower)
            original-right (quadratic-right upper lower)
            substituted-left (quadratic-left sum lower)
            substituted-right (quadratic-right sum lower)
            upper-square (rmul upper upper)
            sum-square (rmul sum sum)
            lower-square (rmul lower lower)
            left-substitution
            (rat-add-respects
             upper-square sum-square lower-square lower-square
             (rat-multiply-respects
              upper sum upper sum upper-to-sum upper-to-sum)
             (rat-reflexive lower-square))
            right-substitution
            (rat-add-respects
             (rmul upper lower) (rmul sum lower)
             (rmul lower upper) (rmul lower sum)
             (rat-multiply-respects
              upper sum lower lower upper-to-sum
              (rat-reflexive lower))
             (rat-multiply-respects
              lower lower upper sum (rat-reflexive lower)
              upper-to-sum))
            substituted-equation
            (rat-transitive
             substituted-left original-left substituted-right
             (rat-symmetric original-left substituted-left
                            left-substitution)
             (rat-transitive
              original-left original-right substituted-right
              equation right-substitution))
            lower-product (rmul lower lower)
            lower-gap (rmul lower 'gap)
            gap-lower (rmul 'gap lower)
            gap-square (rmul 'gap 'gap)
            core
            (radd (radd lower-product lower-product)
                  (radd lower-gap gap-lower))
            expanded (radd core gap-square)
            expanded-to-core
            (rat-transitive
             expanded substituted-left core
             (rat-symmetric
              substituted-left expanded
              (ring/equiv substituted-left expanded))
             (rat-transitive
              substituted-left substituted-right core
              substituted-equation
              (ring/equiv substituted-right core)))
            gap-square-zero
            (app (function/const* 'nnrat/add-cancel-to-zero [])
                 core gap-square expanded-to-core)
            gap-zero
            (app (function/const* 'nnrat/square-zero-reflects [])
                 'gap gap-square-zero)
            remove-gap
            (rat-transitive
             sum (radd lower nnrat-zero) lower
             (rat-add-respects
              lower lower 'gap nnrat-zero
              (rat-reflexive lower) gap-zero)
             (app (function/const* 'nnrat/add-zero-right []) lower))]
        (rat-transitive
         upper sum lower upper-to-sum remove-gap))))))

(def quadratic-equality-reflects-spec
  {:name 'nnrat/quadratic-equality-reflects :universes []
   :type
   (function/forall
    [['positive nnrat] ['negative nnrat]
     ['balanced
      (rat-equivalent
       (quadratic-left 'positive 'negative)
       (quadratic-right 'positive 'negative))]]
    (rat-equivalent 'positive 'negative))
   :value
   (function/lam
    [['positive nnrat] ['negative nnrat]
     ['balanced
      (rat-equivalent
       (quadratic-left 'positive 'negative)
       (quadratic-right 'positive 'negative))]]
    (let [decision (decide-at-most 'negative 'positive)
          goal (rat-equivalent 'positive 'negative)
          motive
          (function/lam
           [['choice bool]]
           (function/arrow (eq-bool decision 'choice) goal))
          at-true
          (function/lam
           [['decided-true (eq-bool decision true-value)]]
           (ordered-quadratic-reflect
            'negative 'positive
            (app (function/const* 'nnrat/decide-at-most-true-sound [])
                 'negative 'positive 'decided-true)
            'balanced))
          at-false
          (function/lam
           [['decided-false (eq-bool decision false-value)]]
           (let [reordered
                 (rat-transitive
                  (quadratic-left 'negative 'positive)
                  (quadratic-left 'positive 'negative)
                  (quadratic-right 'negative 'positive)
                  (ring/equiv
                   (quadratic-left 'negative 'positive)
                   (quadratic-left 'positive 'negative))
                  (rat-transitive
                   (quadratic-left 'positive 'negative)
                   (quadratic-right 'positive 'negative)
                   (quadratic-right 'negative 'positive)
                   'balanced
                   (ring/equiv
                    (quadratic-right 'positive 'negative)
                    (quadratic-right 'negative 'positive))))
                 negative-positive
                 (ordered-quadratic-reflect
                  'positive 'negative
                  (app
                   (function/const*
                    'nnrat/decide-at-most-false-reverse [])
                   'negative 'positive 'decided-false)
                  reordered)]
             (rat-symmetric
              'negative 'positive negative-positive)))]
      (app
       (app (function/const* 'data/Bool.rec [zero-level])
            motive at-false at-true decision)
       (app (function/const* 'equality/reflexive [type-level])
            bool decision))))})

(def definition-specs [])
(def theorem-specs
  [multiply-self-zero-spec
   square-zero-reflects-spec
   quadratic-equality-reflects-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-difference])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'nat/multiply-succ-zero-left :nnrat-add-zero-split zero-split/multiply-succ-zero-left-spec) (extend-spec-if-missing 'nnrat/add-cancel-to-zero :nnrat-add-cancel-zero add-cancel/add-cancel-to-zero-spec) (extend-spec-if-missing 'nnrat/add-zero-right :nnrat-identities identities/add-zero-right-spec) (support/extend-with :nnrat-quadratic-zero theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.quadratic-zero))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
