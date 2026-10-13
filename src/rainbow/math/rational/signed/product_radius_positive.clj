(ns rainbow.math.rational.signed.product-radius-positive
  "Second sub-proof of the limit-product modulus assembly: the magnitude of the radius
  base V = (1+|L|)+|M| has a positive numerator, so nnrat/make-succ-of-positive-numerator
  and analysis/nnrat-radius-cancel apply to it. Axiom-free; additive.

  analysis/product-radius-numerator-positive :
    forall L M, nat/at-most (succ zero)
                  (nnrat/numerator (signed/magnitude (sadd (sadd one (abs L)) (abs M))))

  Chain: 1<=V (signed, via add-monotone + add-zero-right) -> rewrite V ~ from-nnrat(mag V)
  (from-nnrat-magnitude + product-radius-nonneg) -> 1 <= from-nnrat(mag V) [signed/one =def=
  from-nnrat nnrat/one] -> nnrat/at-most nnrat/one (mag V) (from-nnrat-at-most-reverse) ->
  base-at-most (at-most-to-cross) -> den(mag) <= num(mag) (rewrite the *1 factors) ->
  1 <= den(mag) (witness) -> 1 <= num(mag) (nat at-most transitive)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.product-radius-nonneg :as radius-nonneg]
            [rainbow.math.rational.signed.magnitude :as magnitude]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equiv]
            [rainbow.math.rational.signed.geometric-bridge :as geo-bridge]
            [rainbow.math.rational.signed.vector-sup-triangle :as sup-triangle]
            [rainbow.math.rational.signed.distance-triangle :as distance-triangle]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sone (function/const* 'signed/one []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private nnone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denr [x] (app (function/const* 'nnrat/denominator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eqn [x y] (function/equality tl nat x y))
(defn- refl-n [x] (app (function/const* 'equality/reflexive [tl]) nat x))
(defn- sym-n [x y h] (app (function/const* 'equality/symmetric [tl]) nat x y h))
;; signed helpers
(defn- s-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- s-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- s-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- s-eqrefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- add-zero-r [a] (app (function/const* 'signed/add-zero-right []) a))
(defn- abs-nn [x] (app (function/const* 'signed/absolute-nonnegative []) x))
(defn- fnn-magn [x h] (app (function/const* 'signed/from-nnrat-magnitude []) x h))
(defn- radius-nn [L M] (app (function/const* 'analysis/product-radius-nonneg []) L M))
(defn- fnn-le-rev [a b h] (app (function/const* 'signed/from-nnrat-at-most-reverse []) a b h))
(defn- to-cross [a b h] (app (function/const* 'nnrat/at-most-to-cross []) a b h))
;; nat helpers
(defn- n-trans [a b c h1 h2] (app (function/const* 'nat/at-most-transitive []) a b c h1 h2))
(defn- rw-left [x y z heq ham] (app (function/const* 'nat/at-most-rewrite-left []) x y z heq ham))
(defn- rw-right [x y z heq ham] (app (function/const* 'nat/at-most-rewrite-right []) x y z heq ham))
(defn- mul-one-r [a] (app (function/const* 'nat/multiply-one-right []) a))
(defn- add-zero-r-nat [a] (app (function/const* 'algebra/nat-add-zero-right []) a))
(defn- witness [pred val proof] (app (function/const* 'proposition/witness [tl]) nat pred val proof))

(def product-radius-numerator-positive-spec
  {:name 'analysis/product-radius-numerator-positive
   :universes []
   :type (function/forall [['L signed] ['M signed]]
                          (let [V (sadd (sadd sone (abs* 'L)) (abs* 'M))]
                            (nat-le (succ zero) (numr (mag V)))))
   :value
   (function/lam [['L signed] ['M signed]]
                 (let [B (sadd sone (abs* 'L))
                       V (sadd B (abs* 'M))
                       mV (mag V)
                       dm (denr mV) nm (numr mV)
           ;; step 1: 1 <= V
                       one<=B (s-resp (sadd sone szero) sone B B (add-zero-r sone) (s-eqrefl B)
                                      (add-mono sone sone szero (abs* 'L) (s-refl sone) (abs-nn 'L)))  ; 1 <= B
                       B<=V (s-resp (sadd B szero) B V V (add-zero-r B) (s-eqrefl V)
                                    (add-mono B B szero (abs* 'M) (s-refl B) (abs-nn 'M)))            ; B <= V
                       one<=V (s-trans sone B V one<=B B<=V)                                          ; 1 <= V
           ;; step 2-3: 1 <= from-nnrat (mag V)  [signed/one =def= from-nnrat nnrat/one]
                       magEq (fnn-magn V (radius-nn 'L 'M))                                           ; V ~ from-nnrat(mag V)
                       one<=fmag (s-resp sone sone V (fnn mV) (s-eqrefl sone) magEq one<=V)           ; 1 <= from-nnrat(mag V)
           ;; step 4: nnrat/at-most nnrat/one (mag V)
                       nnle (fnn-le-rev nnone mV one<=fmag)                                           ; nnrat/at-most 1 (mag V)
           ;; step 5: base-at-most 1 (mag V) = nat-at-most (mul (succ 0) dm) (mul nm (succ 0))
                       base (to-cross nnone mV nnle)
           ;; step 5b: dm <= nm  (rewrite the *1 factors)
                       dm<=nm (rw-right dm (nmul nm (succ zero)) nm (mul-one-r nm)
                                        (rw-left dm (nmul (succ zero) dm) (nmul nm (succ zero))
                                                 (sym-n (nmul (succ zero) dm) dm (add-zero-r-nat dm))
                                                 base))                                               ; dm <= nm
           ;; step 6: 1 <= dm  (dm = succ (den-pred mV); nadd (succ 0)(den-pred) =def= dm)
                       one<=dm (witness (function/lam [['d nat]] (eqn (nadd (succ zero) 'd) dm))
                                        (denpred mV) (refl-n dm))]                                    ; 1 <= dm
                   (n-trans (succ zero) dm nm one<=dm dm<=nm)))})

(def theorem-specs [product-radius-numerator-positive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.product-radius-nonneg rainbow.math.rational.signed.magnitude rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.signed.geometric-bridge rainbow.math.rational.signed.vector-sup-triangle rainbow.math.rational.signed.distance-triangle])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-product-radius-positive theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.product-radius-positive))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
