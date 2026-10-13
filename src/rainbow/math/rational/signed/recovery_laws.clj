(ns rainbow.math.rational.signed.recovery-laws
  "Two general signed-rational laws that the corpus lacked, proved en route
  to the Gauss-Seidel exactness theorem and promoted here so any module can
  reuse them without depending on an application module.

  - signed/subtract-then-add: the recovery law (a - b) + b ~ a. The corpus
    had only signed/subtract-add-left ((p+l)-(p+r) ~ l-r), a different
    statement; this is the plain recover-the-minuend law.
  - signed/reciprocal-scale-cancel: for a positive rate make(succ p) q,
    scaling by the reciprocal then the value is the identity,
    scale(d, scale(reciprocal d, v)) ~ v.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as rational-division]
            [rainbow.math.rational.signed.add-associative :as add-associative]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-algebra]
            [rainbow.math.rational.signed.rational :as signed-rational]
            [rainbow.math.rational.signed.scale-composition :as scale-composition]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.vector-sup-distance :as sup-distance]
            [rainbow.math.linear.vector.convex-combination :as convex]))

(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sneg [v] (app (function/const* 'signed/negate []) v))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- signed-scale [gain value] (app (function/const* 'signed/scale []) gain value))
(defn- reciprocal [v] (app (function/const* 'nnrat/reciprocal []) v))
(defn- succ [t] (app (function/const* 'data/succ []) t))
(defn- make-raw [np q] (app (function/const* 'nnrat/make []) np q))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- tr [a b c p q] (app (function/const* 'signed/equivalent-transitive []) a b c p q))
(defn- sym [a b p] (app (function/const* 'signed/equivalent-symmetric []) a b p))
(defn- refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- eqof [a b p] (app (function/const* 'signed/equivalent-of-equality []) a b p))
(defn- unfold [a b] (app (function/const* 'signed/subtract-unfold []) a b))
(defn- addresp [a ah b bh pa pb]
  (app (function/const* 'signed/add-respects-equivalence []) a ah b bh pa pb))
(defn- assoc3 [a b c] (app (function/const* 'signed/add-associative []) a b c))
(defn- comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- subself [c] (app (function/const* 'signed/subtract-self-equivalent-zero []) c))
(defn- addzr [v] (app (function/const* 'signed/add-zero-right []) v))

(def subtract-then-add-spec
  "Recovery law the corpus lacked (it had only subtract-add-left):
  (a - b) + b ~ a, via unfold, associativity, negate-self, add-zero."
  {:name 'signed/subtract-then-add :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (seqv (sadd (ssub 'a 'b) 'b) 'a))
   :value
   (function/lam
    [['a signed] ['b signed]]
    (let [nb (sneg 'b) subab (ssub 'a 'b) a-nb (sadd 'a nb)
          unf-ab (eqof subab a-nb (unfold 'a 'b))
          s2 (addresp subab a-nb 'b 'b unf-ab (refl 'b))
          s3 (assoc3 'a nb 'b)
          c4a (comm nb 'b) b-nb (sadd 'b nb) subbb (ssub 'b 'b)
          unf-bb (eqof subbb b-nb (unfold 'b 'b))
          bnb-zero (tr b-nb subbb signed-zero (sym subbb b-nb unf-bb) (subself 'b))
          nbb-zero (tr (sadd nb 'b) b-nb signed-zero c4a bnb-zero)
          s5 (addresp 'a 'a (sadd nb 'b) signed-zero (refl 'a) nbb-zero)
          s6 (addzr 'a)]
      (tr (sadd subab 'b) (sadd a-nb 'b) 'a s2
          (tr (sadd a-nb 'b) (sadd 'a (sadd nb 'b)) 'a s3
              (tr (sadd 'a (sadd nb 'b)) (sadd 'a signed-zero) 'a s5 s6)))))})

(def reciprocal-scale-cancel-spec
  "For a positive rate make(succ p) q, scaling by the reciprocal then the
  value is the identity: scale(d, scale(recip d, v)) ~ v -- via
  scale-composition, divide-self-positive, scale-one."
  {:name 'signed/reciprocal-scale-cancel :universes []
   :type (function/forall
          [['p nat] ['q nat] ['value signed]]
          (let [d (make-raw (succ 'p) 'q)]
            (seqv (signed-scale d (signed-scale (reciprocal d) 'value)) 'value)))
   :value
   (function/lam
    [['p nat] ['q nat] ['value signed]]
    (let [d (make-raw (succ 'p) 'q) rd (reciprocal d)
          comp (app (function/const* 'signed/scale-composition []) d rd 'value)
          dself (app (function/const* 'nnrat/divide-self-positive []) 'p 'q)
          rate-rw (app (function/const* 'signed/scale-respects-rate-equivalence [])
                       (rmul d rd) nnrat-one 'value dself)
          one-rw (app (function/const* 'signed/scale-one []) 'value)]
      (tr (signed-scale d (signed-scale rd 'value)) (signed-scale (rmul d rd) 'value) 'value
          comp
          (tr (signed-scale (rmul d rd) 'value) (signed-scale nnrat-one 'value) 'value
              rate-rw one-rw))))})

(def definition-specs [])
(def theorem-specs [subtract-then-add-spec reciprocal-scale-cancel-spec])

(defn- guard [env alias extend]
  (if (environment/resolve-id env alias) env (extend env)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (guard 'signed/subtract-unfold signed-rational/extend-environment) (guard 'signed/add-associative add-associative/extend-environment) (guard 'signed/subtract-self-equivalent-zero unit-laws/extend-environment) (guard 'signed/equivalent-of-equality sup-distance/extend-environment) (guard 'signed/add-respects-equivalence signed-algebra/extend-environment) (guard 'signed/scale-composition scale-composition/extend-environment) (guard 'signed/scale-one convex/extend-environment) (support/extend-with :signed-recovery-laws (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.recovery-laws))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
