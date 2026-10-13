(ns rainbow.math.finite.markov-geometric-convergence
  "Iterates converge to the stationary distribution at geometric rate.

  Brick 3 of the convergence half: under normalized rows and a certified
  Dobrushin bound rho, the total variation between the n-th iterate of
  any start distribution and a stationary distribution of equal total
  mass is at most rho^n times the initial total variation. The proof
  combines brick 1 (a stationary distribution is fixed by every iterate)
  with brick 2 (geometric decay between iterate pairs) at the stationary
  target.

  Scope, stated so nobody over-quotes it: this is an explicit geometric
  ENVELOPE toward the stationary target in exact rationals. It is not a
  mixing-time statement, makes no claim for rho at or above one (the
  envelope is then vacuous but true), and the rate-null packaging in the
  analysis vocabulary is deliberately deferred until a consumer needs
  it. Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.markov-geometric-decay :as decay]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.finite.markov-stationary-iterate :as fixed]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
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
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- total-variation [element states left right]
  (app (function/const* 'markov/nnrat-total-variation [U])
       element states left right))
(defn- kernel-iterate [element states kernel steps mass]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- order-respects [left eql right eqr same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left eql right eqr same-left same-right ordered))

(def iterate-converges-to-stationary-spec
  "TV(iterate n start, pi) <= power rho n * TV(start, pi) for stationary pi."
  {:name 'markov/nnrat-kernel-iterate-geometric-convergence-to-stationary
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['rho nnrat]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel) (from-nnrat 'rho))]
     ['start (mass-type 'S)] ['pi (mass-type 'S)]
     ['pi-stationary (stationary 'S 'states 'kernel 'pi)]
     ['equal-total-mass (req (total-mass 'S 'states 'start)
                             (total-mass 'S 'states 'pi))]
     ['steps nat]]
    (rle (total-variation 'S 'states
                          (kernel-iterate 'S 'states 'kernel 'steps 'start)
                          'pi)
         (rmul (rpow 'rho 'steps)
               (total-variation 'S 'states 'start 'pi))))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['rho nnrat]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel) (from-nnrat 'rho))]
     ['start (mass-type 'S)] ['pi (mass-type 'S)]
     ['pi-stationary (stationary 'S 'states 'kernel 'pi)]
     ['equal-total-mass (req (total-mass 'S 'states 'start)
                             (total-mass 'S 'states 'pi))]
     ['steps nat]]
    (let [it-start (kernel-iterate 'S 'states 'kernel 'steps 'start)
          it-pi (kernel-iterate 'S 'states 'kernel 'steps 'pi)
          tv-to-pi (total-variation 'S 'states it-start 'pi)
          tv-pair (total-variation 'S 'states it-start it-pi)
          envelope (rmul (rpow 'rho 'steps)
                         (total-variation 'S 'states 'start 'pi))
          ;; brick 1 pointwise, symmetric: pi s ~ iterate n pi s.
          pi-fixed
          (function/lam
           [['state 'S]]
           (equivalent-symmetric
            (app it-pi 'state) (app 'pi 'state)
            (app (function/const* 'markov/nnrat-stationary-iterate-fixed [U])
                 'S 'states 'kernel 'pi 'pi-stationary 'steps 'state)))
          ;; TV(iterate n start, pi) ~ TV(iterate n start, iterate n pi).
          collapse
          (app (function/const*
                'markov/nnrat-total-variation-respects-pointwise-equivalent
                [U])
               'S 'states
               it-start it-start 'pi it-pi
               (function/lam
                [['state 'S]]
                (equivalent-reflexive (app it-start 'state)))
               pi-fixed)
          ;; brick 2 at the pair (start, pi).
          decayed
          (app (function/const*
                'markov/nnrat-kernel-iterate-total-variation-decay [U])
               'S 'states 'kernel 'rho
               'normalized 'coefficient-bound
               'start 'pi 'equal-total-mass 'steps)]
      (order-respects
       tv-to-pi tv-pair envelope envelope
       collapse
       (equivalent-reflexive envelope)
       decayed)))})

(def definition-specs [])
(def theorem-specs [iterate-converges-to-stationary-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      decay/extend-environment
      ;; Brick 1 and the stationarity predicate enter per-spec: the decay
      ;; chain already carries the contraction world, and re-entering the
      ;; stationarity/composition/iteration extenders wholesale would
      ;; re-install shared upstreams.
      (extend-spec-if-missing
       'markov/nnrat-stationary
       :finite-markov-stationarity stationarity/stationary-spec)
      (extend-spec-if-missing
       'markov/nnrat-stationary-iterate-fixed
       :finite-markov-stationary-iterate fixed/stationary-iterate-fixed-spec)
      (support/extend-with :finite-markov-geometric-convergence
                           theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
