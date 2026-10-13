(ns rainbow.math.rational.signed.distance-negate
  "d(-a,-b) ~ d(a,b): distance is invariant under negating both points. Needed for the
  negative branch of limit-product's distance-multiply (brick 2). Axiom-free; additive.

  Proof: distance p q = |p - q|; subtract(-a,-b) ~ negate(a-b) (from negate-additive on
  a and (negate b), since subtract reduces to add-with-negated-second); then
  |negate(a-b)| ~ |a-b| via absolute-negate."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute-algebra :as absolute-algebra]
            [rainbow.math.rational.signed.distance :as distance]
            [rainbow.math.rational.signed.negate-additive :as negate-additive]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- neg* [x] (app (function/const* 'signed/negate []) x))
(defn- sub* [a b] (app (function/const* 'signed/subtract []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist* [a b] (app (function/const* 'signed/distance []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eq-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- abs-resp [a b h] (app (function/const* 'signed/absolute-respects-equivalence []) a b h))
(defn- abs-neg [x] (app (function/const* 'signed/absolute-negate []) x))
(defn- neg-add [a b] (app (function/const* 'signed/negate-additive []) a b))

(def distance-negate-both-spec
  {:name 'signed/distance-negate-both
   :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (seqv (dist* (neg* 'a) (neg* 'b)) (dist* 'a 'b)))
   :value
   (function/lam [['a signed] ['b signed]]
                 (let [;; negate-additive a (negate b) : seqv (negate (a + -b)) ((-a) + -(-b))
           ;; with subtract p q =def= p + (-q): LHS = negate(a-b), RHS = subtract(-a)(-b)
                       H (neg-add 'a (neg* 'b))                    ; seqv (negate (a - b)) (subtract (-a) (-b))
                       s1 (abs-resp (sub* (neg* 'a) (neg* 'b)) (neg* (sub* 'a 'b))
                                    (eq-sym (neg* (sub* 'a 'b)) (sub* (neg* 'a) (neg* 'b)) H))  ; |subtract(-a)(-b)| ~ |negate(a-b)|
                       s2 (abs-neg (sub* 'a 'b))]                  ; |negate(a-b)| ~ |a-b|
                   (eq-trans (abs* (sub* (neg* 'a) (neg* 'b))) (abs* (neg* (sub* 'a 'b))) (abs* (sub* 'a 'b))
                             s1 s2)))})

(def theorem-specs [distance-negate-both-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.rational.signed.negate-additive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-distance-negate theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.distance-negate))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
