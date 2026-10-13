(ns rainbow.math.rational.convergence
  "Convergence of a nonnegative-rational distance sequence to its limit, with an
  explicit rational modulus -- the analysis layer above the geometric contraction
  bound. A distance sequence `seq : Nat -> nnrat` (the distance d(x_n, limit))
  converges when, for every accuracy epsilon, a modulus tells how far to iterate:

      converges-to seq modulus  :=
        forall epsilon. forall n. (modulus epsilon <= n) -> (seq n <= epsilon)

  using the native Prop orders `nat/at-most` and `nnrat/at-most`. No absolute
  value is needed (the distance is already nonnegative) and no reals are needed
  (the modulus is Nat-valued). For a geometric contraction (seq n = gamma^n * d0
  with rational gamma < 1) the modulus is the least n with gamma^n * d0 <=
  epsilon, so convergence is exact rational/Nat data. Composed with a fixed-point
  uniqueness result this gives proved value-iteration convergence.

  Requires `nat/at-most` and `nnrat/at-most` in the environment."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def prop 'Prop)

(defn- nat-at-most [l r] (function/app (function/const* 'nat/at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- converges-to [seq modulus]
  (function/app (function/const* 'convergence/converges-to []) seq modulus))

;; The distance sequence and modulus signatures.
(def seq-type (function/arrow nat nnrat))
(def modulus-type (function/arrow nnrat nat))

;; The body of converges-to, as a term (for the unfold law).
(defn- converges-body [seq modulus]
  (function/forall
   [['epsilon nnrat] ['n nat]]
   (function/arrow (nat-at-most (function/app modulus 'epsilon) 'n)
                   (nnrat-at-most (function/app seq 'n) 'epsilon))))

;; Definitions --------------------------------------------------------------

;; converges-to seq modulus :=
;;   forall eps n. (modulus eps <= n) -> (seq n <= eps)
(def converges-to-spec
  {:name 'convergence/converges-to :kind :definition :universes []
   :type (function/arrow seq-type modulus-type prop)
   :value (function/lam [['seq seq-type] ['modulus modulus-type]]
                        (converges-body 'seq 'modulus))})

(def definition-specs [converges-to-spec])

;; Theorems -----------------------------------------------------------------

(def converges-to-unfold-spec
  {:name 'convergence/converges-to-unfold :universes []
   :type (function/forall
          [['seq seq-type] ['modulus modulus-type]]
          (equality prop (converges-to 'seq 'modulus)
                    (converges-body 'seq 'modulus)))
   :value (function/lam [['seq seq-type] ['modulus modulus-type]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         prop (converges-to 'seq 'modulus)))})

(def theorem-specs [converges-to-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :rational-convergence (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.convergence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
