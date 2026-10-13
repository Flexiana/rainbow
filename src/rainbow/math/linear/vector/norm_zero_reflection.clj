(ns rainbow.math.linear.vector.norm-zero-reflection
  "Zero squared norm reflects componentwise zero for finite signed vectors.

    norm/equivalent-zero-like-of-norm-squared-zero
    norm/equivalent-zero-like-of-is-norm-zero

  The conclusion uses vector/zero-like, not the empty vector: it preserves the
  input dimension and vector/equivalent proves every component equivalent to
  signed zero.  List induction splits each zero sum into the nonnegative head
  square and tail squared norm, reflects the head square, and recurses.  Native
  and axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancel-zero :as add-cancel]
            [rainbow.math.rational.nnrat.add-zero-split :as zero-split]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.quadratic-zero :as quadratic]
            [rainbow.math.rational.signed.add-zero-reflection :as add-reflection]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.square-zero :as square-zero]
            [rainbow.math.linear.vector.additive-units :as units]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]
            [rainbow.math.linear.vector.norm-nonnegative :as nonnegative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rnum [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- rden [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- nat-multiply [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- is-norm [values candidate]
  (app (function/const* 'norm/is-norm []) values candidate))
(defn- nonnegative [value]
  (app (function/const* 'signed/nonnegative []) value))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(defn- signed-cross-reflexivity [left right]
  (let [lhs (radd (positive left) (negative right))
        rhs (radd (positive right) (negative left))]
    (app (function/const* 'equality/reflexive [type-level])
         nat (nat-multiply (rnum lhs) (rden rhs)))))

(def equivalent-zero-like-of-norm-squared-zero-spec
  {:name 'norm/equivalent-zero-like-of-norm-squared-zero :universes []
   :type
   (function/forall
    [['values vector-type]
     ['norm-zero
      (signed-equivalent (norm-squared 'values) signed-zero)]]
    (vector-equivalent 'values (zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (function/arrow
            (signed-equivalent (norm-squared 'current) signed-zero)
            (vector-equivalent 'current (zero-like 'current))))
          base
          (function/lam
           [['empty-norm-zero
             (signed-equivalent
              (norm-squared (nil-vector)) signed-zero)]]
           trivial)
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-reflection (app motive 'tail)]]
           (function/lam
            [['current-norm-zero
              (signed-equivalent
               (norm-squared
                (app (function/const* 'data/cons [type-level])
                     signed 'head 'tail))
               signed-zero)]]
            (let [head-square (signed-multiply 'head 'head)
                  tail-square (norm-squared 'tail)
                  head-square-nonnegative
                  (app (function/const* 'signed/square-nonnegative [])
                       'head)
                  tail-square-nonnegative
                  (app
                   (function/const* 'norm/norm-squared-nonnegative [])
                   'tail)
                  head-square-zero
                  (app
                   (function/const*
                    'signed/add-zero-split-nonnegative-left [])
                   head-square tail-square
                   head-square-nonnegative tail-square-nonnegative
                   'current-norm-zero)
                  tail-square-zero
                  (app
                   (function/const*
                    'signed/add-zero-split-nonnegative-right [])
                   head-square tail-square
                   head-square-nonnegative tail-square-nonnegative
                   'current-norm-zero)
                  head-zero
                  (app (function/const* 'signed/square-zero-reflects [])
                       'head head-square-zero)
                  tail-zero (app 'tail-reflection tail-square-zero)]
              (conjoin
               (signed-equivalent 'head signed-zero)
               (vector-equivalent 'tail (zero-like 'tail))
               head-zero tail-zero))))]
      (list-rec motive base step 'values)))})

(def equivalent-zero-like-of-is-norm-zero-spec
  {:name 'norm/equivalent-zero-like-of-is-norm-zero :universes []
   :type
   (function/forall
    [['values vector-type]
     ['zero-is-norm (is-norm 'values signed-zero)]]
    (vector-equivalent 'values (zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]
     ['zero-is-norm (is-norm 'values signed-zero)]]
    (let [zero-square (signed-multiply signed-zero signed-zero)
          vector-square (norm-squared 'values)
          vector-square-zero
          (signed-transitive
           vector-square zero-square signed-zero
           (signed-symmetric
            zero-square vector-square 'zero-is-norm)
           (signed-cross-reflexivity zero-square signed-zero))]
      (app
       (function/const*
        'norm/equivalent-zero-like-of-norm-squared-zero [])
       'values vector-square-zero)))})

(def definition-specs [])
(def theorem-specs
  [equivalent-zero-like-of-norm-squared-zero-spec
   equivalent-zero-like-of-is-norm-zero-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.norm-nonnegative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'nat/multiply-succ-zero-left :nnrat-add-zero-split zero-split/multiply-succ-zero-left-spec) (extend-spec-if-missing 'nnrat/add-cancel-to-zero :nnrat-add-cancel-zero add-cancel/add-cancel-to-zero-spec) (extend-spec-if-missing 'nnrat/add-zero-right :nnrat-identities identities/add-zero-right-spec) (extend-spec-if-missing 'nnrat/add-zero-left :nnrat-identities identities/add-zero-left-spec) (extend-spec-if-missing 'nat/multiply-self-zero :nnrat-quadratic-zero quadratic/multiply-self-zero-spec) (extend-spec-if-missing 'nnrat/square-zero-reflects :nnrat-quadratic-zero quadratic/square-zero-reflects-spec) (extend-spec-if-missing 'nnrat/quadratic-equality-reflects :nnrat-quadratic-zero quadratic/quadratic-equality-reflects-spec) (extend-spec-if-missing 'signed/square-zero-reflects :signed-square-zero square-zero/square-zero-reflects-spec) add-reflection/extend-environment (extend-spec-if-missing 'signed/equivalent-transitive :signed-map-sum-algebra map-sum/equivalent-transitive-spec) (extend-spec-if-missing 'vector/zero-like :vector-additive-units units/zero-like-spec) (extend-spec-if-missing 'vector/equivalent :vector-equivalence vector-equivalence/equivalent-spec) (support/extend-with :vector-norm-zero-reflection theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.norm-zero-reflection))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
