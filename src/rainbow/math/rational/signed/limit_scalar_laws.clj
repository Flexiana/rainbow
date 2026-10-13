(ns rainbow.math.rational.signed.limit-scalar-laws
  "Axiom-free constant and nonnegative-scalar laws for signed order bands.

  `analysis/converges` quantifies over every signed radius, including negative
  radii.  A constant sequence therefore cannot inhabit it: `close C eps C`
  entails that eps is nonnegative.  This module leaves that committed predicate
  untouched and supplies the non-vacuous radius-corrected predicate
  `analysis/converges-nonnegative`, together with its constant limit law.

  Scaling does not require changing the source predicate.  At every radius and
  index admitted by a source convergence proof, the committed
  `analysis/close-scale-nonnegative` theorem gives the corresponding band with
  center, radius, and sequence value all multiplied by `from-nnrat c`."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-scale :as scale]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))
(def zero-nat (function/const* 'data/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- nonnegative [v] (app (function/const* 'signed/nonnegative []) v))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M]
  (app (function/const* 'analysis/converges []) s L M))
(defn- converges-nonnegative [s L M]
  (app (function/const* 'analysis/converges-nonnegative []) s L M))

(defn- rat-refl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       a b c first second))
(defn- rat-add-assoc [a b c]
  (app (function/const* 'nnrat/add-associative []) a b c))
(defn- rat-add-comm [a b]
  (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-add-monotone [a ah b bh ordered-a ordered-b]
  (app (function/const* 'nnrat/add-monotone [])
       a ah b bh ordered-a ordered-b))
(defn- rat-at-most-reflexive [v]
  (app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))

(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))

;; (a+b)+c ~ (a+c)+b, assembled from the installed nnrat laws.
(defn- rat-reorder-three [a b c]
  (let [start (radd (radd a b) c)
        first (radd a (radd b c))
        second (radd a (radd c b))
        finish (radd (radd a c) b)]
    (rat-trans
     start first finish
     (rat-add-assoc a b c)
     (rat-trans
      first second finish
      (rat-add-respects a a (radd b c) (radd c b)
                        (rat-refl a) (rat-add-comm b c))
      (rat-sym finish second (rat-add-assoc a c b))))))

;; ---- radius-corrected convergence -----------------------------------------

(def converges-nonnegative-spec
  {:name 'analysis/converges-nonnegative :kind :definition :universes []
   :type (function/arrow sig-seq signed modulus 'Prop)
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['M modulus]]
    (function/forall
     [['eps signed] ['n nat]]
     (function/arrow
      (nonnegative 'eps)
      (nat-at-most (app 'M 'eps) 'n)
      (close 'L 'eps (app 's 'n)))))})

;; A point is in its own eps-band exactly in the direction needed here when
;; eps is nonnegative.  Both signed comparisons normalize to
;;   (P_C + N_C) + N_eps <= (P_C + N_C) + P_eps.
(def close-self-nonnegative-spec
  {:name 'analysis/close-self-nonnegative :universes []
   :type
   (function/forall
    [['C signed] ['eps signed]
     ['eps-nonnegative (nonnegative 'eps)]]
    (close 'C 'eps 'C))
   :value
   (function/lam
    [['C signed] ['eps signed]
     ['eps-nonnegative (nonnegative 'eps)]]
    (let [P (pos 'C) N (neg 'C) Pe (pos 'eps) Ne (neg 'eps)
          common (radd P N)
          core-left (radd common Ne)
          core-right (radd common Pe)
          core
          (rat-add-monotone common common Ne Pe
                            (rat-at-most-reflexive common)
                            'eps-nonnegative)

          low (ssub 'C 'eps)
          low-goal-left (radd (radd P Ne) N)
          low-goal-right (radd P (radd N Pe))
          low-left-same (rat-reorder-three P Ne N)
          low-right-same
          (rat-sym core-right low-goal-right (rat-add-assoc P N Pe))
          low<=C
          (rat-at-most-respects
           low-goal-left core-left low-goal-right core-right
           low-left-same low-right-same core)

          high (sadd 'C 'eps)
          high-goal-left (radd P (radd N Ne))
          high-goal-right (radd (radd P Pe) N)
          high-left-same
          (rat-sym core-left high-goal-left (rat-add-assoc P N Ne))
          high-right-same (rat-reorder-three P Pe N)
          C<=high
          (rat-at-most-respects
           high-goal-left core-left high-goal-right core-right
           high-left-same high-right-same core)]
      (conjoin (sle low 'C) (sle 'C high) low<=C C<=high)))})

(def limit-const-spec
  {:name 'analysis/limit-const :universes []
   :type
   (function/forall
    [['C signed]]
    (converges-nonnegative
     (function/lam [['n nat]] 'C)
     'C
     (function/lam [['eps signed]] zero-nat)))
   :value
   (function/lam
    [['C signed]]
    (function/lam
     [['eps signed] ['n nat]
      ['eps-nonnegative (nonnegative 'eps)]
      ['large-enough (nat-at-most zero-nat 'n)]]
     (app (function/const* 'analysis/close-self-nonnegative [])
          'C 'eps 'eps-nonnegative)))})

;; ---- same-modulus scaled bands --------------------------------------------

(def scaled-sequence-close-to-scaled-limit-spec
  {:name 'analysis/scaled-sequence-close-to-scaled-limit :universes []
   :type
   (function/forall
    [['c nnrat] ['s sig-seq] ['L signed] ['M modulus]
     ['s-converges (converges 's 'L 'M)]
     ['eps signed] ['n nat]
     ['large-enough (nat-at-most (app 'M 'eps) 'n)]]
    (close (smul (from-nnrat 'c) 'L)
           (smul (from-nnrat 'c) 'eps)
           (smul (from-nnrat 'c) (app 's 'n))))
   :value
   (function/lam
    [['c nnrat] ['s sig-seq] ['L signed] ['M modulus]
     ['s-converges (converges 's 'L 'M)]
     ['eps signed] ['n nat]
     ['large-enough (nat-at-most (app 'M 'eps) 'n)]]
    (app (function/const* 'analysis/close-scale-nonnegative [])
         'c 'L 'eps (app 's 'n)
         (app 's-converges 'eps 'n 'large-enough)))})

(def definition-specs [converges-nonnegative-spec])
(def theorem-specs
  [close-self-nonnegative-spec
   limit-const-spec
   scaled-sequence-close-to-scaled-limit-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      scale/extend-environment
      (support/extend-with :signed-limit-scalar-laws
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
