(ns rainbow.algorithms.proofs.net-flow
  "AHoF net flow / net present value: the signed balance of inflows against
  outflows,

      net inflow outflow = inflow - outflow,

  the exact-rational primitive behind net-reward MDPs, cash-flow / NPV
  accounting, and constraint residuals. Signed subtraction stores the balance as
  a Grothendieck pair (positive, negative) that is not canonical, so worked net
  values are proved on the signed cross-product equivalence signed/equivalent
  (discharged by reflexivity on the reduced nat cross-product), and a surplus
  (inflow >= outflow) is certified nonnegative via the decidable rational order.
  Discounting a cash-flow stream is an executable concern; what is proved here is
  the net computation, worked balances, and the surplus-nonnegativity guarantee.

  Requires signed/subtract, signed/equivalent, signed/nonnegative, nnrat/at-most,
  and the decidable nnrat order (all carried by the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.net-flow`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- signed-numeral [n]
  (function/app (function/const* 'signed/from-nnrat [])
                (function/app (function/const* 'nnrat/make []) (data-nat n)
                              (data-nat 0))))

(defn- s-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- s-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nnrat-denominator [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- signed-subtract [l r]
  (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-equivalent [l r]
  (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-nonnegative [v]
  (function/app (function/const* 'signed/nonnegative []) v))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- net [inflow outflow]
  (function/app (function/const* 'net-flow/net []) inflow outflow))

;; A worked signed/equivalent proof: it unfolds to a nat cross-product equality,
;; discharged by reflexivity when both sides reduce to the same nat.
(defn- signed-cross-reflexivity [left right]
  (let [lhs (nnrat-add (s-positive left) (s-negative right))
        rhs (nnrat-add (s-positive right) (s-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (nnrat-numerator lhs)
                                    (nnrat-denominator rhs)))))

;; signed/nonnegative v unfolds to (negative v <= positive v); discharge by the
;; decidable order.
(defn- nonnegative-proof [value]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                (s-negative value) (s-positive value)
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most (s-negative value)
                                                   (s-positive value)))))

;; Definitions --------------------------------------------------------------

;; net inflow outflow = inflow - outflow
(def net-spec
  {:name 'net-flow/net :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['inflow signed] ['outflow signed]]
                        (signed-subtract 'inflow 'outflow))})

(def definition-specs [net-spec])

;; Theorems -----------------------------------------------------------------

(def net-unfold-spec
  {:name 'net-flow/net-unfold :universes []
   :type (function/forall
          [['inflow signed] ['outflow signed]]
          (equality signed (net 'inflow 'outflow)
                    (signed-subtract 'inflow 'outflow)))
   :value (function/lam [['inflow signed] ['outflow signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (net 'inflow 'outflow)))})

;; A surplus balance: net(5, 3) ~ 2.
(def net-surplus-example-spec
  {:name 'net-flow/net-surplus-example :universes []
   :type (signed-equivalent (net (signed-numeral 5) (signed-numeral 3))
                            (signed-numeral 2))
   :value (signed-cross-reflexivity
           (net (signed-numeral 5) (signed-numeral 3))
           (signed-numeral 2))})

;; A larger surplus: net(7, 2) ~ 5.
(def net-larger-surplus-example-spec
  {:name 'net-flow/net-larger-surplus-example :universes []
   :type (signed-equivalent (net (signed-numeral 7) (signed-numeral 2))
                            (signed-numeral 5))
   :value (signed-cross-reflexivity
           (net (signed-numeral 7) (signed-numeral 2))
           (signed-numeral 5))})

;; Surplus certificate: when inflow >= outflow the net balance is nonnegative.
(def net-surplus-nonnegative-spec
  {:name 'net-flow/net-surplus-nonnegative :universes []
   :type (signed-nonnegative (net (signed-numeral 5) (signed-numeral 3)))
   :value (nonnegative-proof (net (signed-numeral 5) (signed-numeral 3)))})

(def theorem-specs
  [net-unfold-spec net-surplus-example-spec net-larger-surplus-example-spec
   net-surplus-nonnegative-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :net-flow (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.net-flow))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
