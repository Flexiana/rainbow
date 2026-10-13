(ns rainbow.algorithms.proofs.ahof.gauss-seidel
  "Gauss-Seidel coordinate update (Kochenderfer Optimization O24.1), the
  last of the four signed-cluster algorithms deferred in August.

  The Gauss-Seidel sweep updates each coordinate against the current
  values of the others: x_i = (b_i - sum_{j!=i} a_ij x_j) / a_ii. The
  August note deferred this expecting signed division; keeping the
  diagonal a POSITIVE nnrat makes the division an nnrat reciprocal and
  the update a signed scale, so no signed division is needed:
  `optimization/gauss-seidel-step diagonal target off-diagonal =
   signed/scale (nnrat/reciprocal diagonal) (signed/subtract target off-diagonal)`.
  The worked theorem proves one 2-variable coordinate update -- diagonal
  a11=2, target b1=4, off-diagonal a12*x2 = 1 -> (4-1)/2 = 3/2 -- by
  signed cross-product reflexivity. Chains rational-division; native and
  axiom-free on D63. A proved native module; formal ledger crediting is
  the separate catalog follow-up.

  With this the four August-deferred signed-cluster algorithms (LQR,
  NNLS, Stieltjes, Gauss-Seidel) are all proved. This module also proves
  the UNIVERSAL exactness property -- the update satisfies its coordinate
  equation for every target and off-diagonal -- and two general signed
  lemmas proved en route that fill genuine corpus gaps (a subtract-then-
  add recovery law and reciprocal-scale cancellation); those two are
  general enough to promote to a core signed module later."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as rational-division]
            [rainbow.math.rational.signed.recovery-laws :as recovery-laws]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- numeral [n]
  (loop [remaining (long n) term (function/const* 'data/zero [])]
    (if (zero? remaining)
      term
      (recur (dec remaining) (app (function/const* 'data/succ []) term)))))
(defn- nnrat-make [num den-pred]
  (app (function/const* 'nnrat/make []) (numeral num) (numeral den-pred)))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- reciprocal [v] (app (function/const* 'nnrat/reciprocal []) v))
(defn- signed-scale [gain state] (app (function/const* 'signed/scale []) gain state))
(defn- signed-subtract [a b] (app (function/const* 'signed/subtract []) a b))
(defn- signed-equivalent [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- signed-positive [v] (app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (app (function/const* 'signed/negative []) v))
(defn- nnrat-add [a b] (app (function/const* 'nnrat/add []) a b))
(defn- numerator [v] (app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [a b] (app (function/const* 'nat/multiply []) a b))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (app (function/const* 'equality/reflexive [type-level])
         nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def gauss-seidel-step-spec
  {:name 'optimization/gauss-seidel-step :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow nnrat signed signed signed)
   :value (function/lam
           [['diagonal nnrat] ['target signed] ['off-diagonal signed]]
           (signed-scale (reciprocal 'diagonal)
                         (signed-subtract 'target 'off-diagonal)))})

(defn- step [diagonal target off-diagonal]
  (app (function/const* 'optimization/gauss-seidel-step [])
       diagonal target off-diagonal))

(def gauss-seidel-step-worked-spec
  "One coordinate update: diagonal 2, target 4, off-diagonal 1 -> 3/2."
  {:name 'optimization/gauss-seidel-step-worked :universes []
   :type (signed-equivalent
          (step (nnrat-make 2 0) (from-nnrat (nnrat-make 4 0))
                (from-nnrat (nnrat-make 1 0)))
          (from-nnrat (nnrat-make 3 1)))
   :value (signed-equivalent-cross
           (step (nnrat-make 2 0) (from-nnrat (nnrat-make 4 0))
                 (from-nnrat (nnrat-make 1 0)))
           (from-nnrat (nnrat-make 3 1)))})

;; ---- exactness, built on the promoted general lemmas -----------------------
;; signed/subtract-then-add and signed/reciprocal-scale-cancel now live in
;; rainbow.math.rational.signed.recovery-laws (a core signed module) rather than
;; here; this module chains that module and consumes them.

(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- tr [a b c p q] (app (function/const* 'signed/equivalent-transitive []) a b c p q))
(defn- addresp [a ah b bh pa pb]
  (app (function/const* 'signed/add-respects-equivalence []) a ah b bh pa pb))
(defn- succ [t] (app (function/const* 'data/succ []) t))
(defn- make-raw [np q] (app (function/const* 'nnrat/make []) np q))

(def gauss-seidel-step-exact-spec
  "The UNIVERSAL defining property: for a positive diagonal, the update
  satisfies its coordinate equation exactly --
  diagonal * step + off-diagonal ~ target, for every target and
  off-diagonal. The crux cancels the reciprocal scaling to the residual,
  then the recovery law adds the off-diagonal back to the target."
  {:name 'optimization/gauss-seidel-step-exact :universes []
   :type (function/forall
          [['p nat] ['q nat] ['target signed] ['off-diagonal signed]]
          (let [d (make-raw (succ 'p) 'q)]
            (seqv (sadd (signed-scale d (step d 'target 'off-diagonal)) 'off-diagonal)
                  'target)))
   :value
   (function/lam
    [['p nat] ['q nat] ['target signed] ['off-diagonal signed]]
    (let [d (make-raw (succ 'p) 'q)
          residual (ssub 'target 'off-diagonal)
          crux (app (function/const* 'signed/reciprocal-scale-cancel [])
                    'p 'q residual)
          scaled-step (signed-scale d (step d 'target 'off-diagonal))
          s1 (addresp scaled-step residual 'off-diagonal 'off-diagonal
                      crux (refl 'off-diagonal))
          recovery (app (function/const* 'signed/subtract-then-add [])
                        'target 'off-diagonal)]
      (tr (sadd scaled-step 'off-diagonal) (sadd residual 'off-diagonal) 'target
          s1 recovery)))})

(def definition-specs [gauss-seidel-step-spec])
(def theorem-specs [gauss-seidel-step-worked-spec
                    gauss-seidel-step-exact-spec])

(defn extend-environment [env]
  (-> env
      rational-division/extend-environment
      recovery-laws/extend-environment
      (support/extend-with :ahof-gauss-seidel
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
