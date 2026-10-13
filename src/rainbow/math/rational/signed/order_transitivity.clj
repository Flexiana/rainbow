(ns rainbow.math.rational.signed.order-transitivity
  "Real-analysis roadmap step 4: transitivity of the signed-rational order.

  signed/at-most a b is the additive comparison  pos(a) + neg(b) <= pos(b) + neg(a)
  (nnrat order, no primitive subtraction).  Transitivity is the classic argument, now
  fully mechanizable because every ingredient exists:

    a<=b : Pa+Nb <= Pb+Na          b<=c : Pb+Nc <= Pc+Nb
    add them (nnrat/add-monotone) : (Pa+Nb)+(Pb+Nc) <= (Pb+Na)+(Pc+Nb)
    reorder both sides so the shared (Pb+Nb) is isolated (nnrat/add-four-reorder +
      add-commutative, transported by add-/at-most-respects-equivalence) :
        (Pa+Nc)+(Pb+Nb) <= (Pc+Na)+(Pb+Nb)
    cancel the shared summand (step-3 nnrat/at-most-add-right-cancel) :
        Pa+Nc <= Pc+Na   ==   a<=c.

  This is the gate to signed min/max/abs and the epsilon-N convergence predicate.
  Native and axiom-free; chains nnrat-add-monotone, nnrat-add-cancellation, and nnrat-additive-reassociation on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as am]
            [rainbow.math.rational.nnrat.add-cancellation :as ac]
            [rainbow.math.rational.nnrat.additive-reassociation :as rr]))

(def signed (function/const* 'signed/SignedRational []))

(defn- pos [v] (function/app (function/const* 'signed/positive []) v))
(defn- neg [v] (function/app (function/const* 'signed/negative []) v))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- signed-at-most [a b] (function/app (function/const* 'signed/at-most []) a b))
(defn- addmono [a ah b bh ha hb]
  (function/app (function/const* 'nnrat/add-monotone []) a ah b bh ha hb))
(defn- addcomm [x y] (function/app (function/const* 'nnrat/add-commutative []) x y))
(defn- fr [a b c d] (function/app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- addresp [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- atresp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- addcancel [x k y h]
  (function/app (function/const* 'nnrat/at-most-add-right-cancel []) x k y h))
(defn- etrans [x y z p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) x y z p q))
(defn- esym [x y p] (function/app (function/const* 'nnrat/equivalent-symmetric []) x y p))
(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))

(def at-most-transitive-spec
  {:name 'signed/at-most-transitive :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['h1 (signed-at-most 'a 'b)] ['h2 (signed-at-most 'b 'c)]]
          (signed-at-most 'a 'c))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['h1 (signed-at-most 'a 'b)] ['h2 (signed-at-most 'b 'c)]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b) Pc (pos 'c) Nc (neg 'c)
          ;; (Pa+Nb)+(Pb+Nc) <= (Pb+Na)+(Pc+Nb)
          step-sum (addmono (radd Pa Nb) (radd Pb Na) (radd Pb Nc) (radd Pc Nb) 'h1 'h2)
          ;; E1 : (Pa+Nc)+(Pb+Nb) ~ (Pa+Nb)+(Pb+Nc)
          E1 (etrans (radd (radd Pa Nc) (radd Pb Nb))
                     (radd (radd Pa Pb) (radd Nc Nb))
                     (radd (radd Pa Nb) (radd Pb Nc))
                     (fr Pa Nc Pb Nb)
                     (etrans (radd (radd Pa Pb) (radd Nc Nb))
                             (radd (radd Pa Pb) (radd Nb Nc))
                             (radd (radd Pa Nb) (radd Pb Nc))
                             (addresp (radd Pa Pb) (radd Pa Pb) (radd Nc Nb) (radd Nb Nc)
                                      (erefl (radd Pa Pb)) (addcomm Nc Nb))
                             (esym (radd (radd Pa Nb) (radd Pb Nc))
                                   (radd (radd Pa Pb) (radd Nb Nc))
                                   (fr Pa Nb Pb Nc))))
          ;; E2 : (Pc+Na)+(Pb+Nb) ~ (Pb+Na)+(Pc+Nb)
          E2 (etrans (radd (radd Pc Na) (radd Pb Nb))
                     (radd (radd Pc Pb) (radd Na Nb))
                     (radd (radd Pb Na) (radd Pc Nb))
                     (fr Pc Na Pb Nb)
                     (etrans (radd (radd Pc Pb) (radd Na Nb))
                             (radd (radd Pb Pc) (radd Na Nb))
                             (radd (radd Pb Na) (radd Pc Nb))
                             (addresp (radd Pc Pb) (radd Pb Pc) (radd Na Nb) (radd Na Nb)
                                      (addcomm Pc Pb) (erefl (radd Na Nb)))
                             (esym (radd (radd Pb Na) (radd Pc Nb))
                                   (radd (radd Pb Pc) (radd Na Nb))
                                   (fr Pb Na Pc Nb))))
          ;; transport step-sum's endpoints to the (.. + (Pb+Nb)) forms
          transported (atresp (radd (radd Pa Nc) (radd Pb Nb))
                              (radd (radd Pa Nb) (radd Pb Nc))
                              (radd (radd Pc Na) (radd Pb Nb))
                              (radd (radd Pb Na) (radd Pc Nb))
                              E1 E2 step-sum)]
      ;; cancel the shared (Pb+Nb)
      (addcancel (radd Pa Nc) (radd Pb Nb) (radd Pc Na) transported)))})

(def definition-specs [])
(def theorem-specs [at-most-transitive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-order-transitivity (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.order-transitivity))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
