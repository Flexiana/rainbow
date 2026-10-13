(ns rainbow.math.rational.signed.order-respects
  "Equivalence transport for signed order and signed-sequence convergence.

  The order proof uses two copies of the reorder-and-cancel argument from
  signed/at-most-transitive.  First it transports the left endpoint through a signed
  equivalence, then it transports the right endpoint.  In each pass an equivalence is
  viewed as an nnrat inequality, added to the current order proof, reordered so a
  common right summand is visible, and cancelled.

  The convergence theorem is the first limit law unlocked by that transport: replacing
  every term of a convergent signed sequence by an equivalent term preserves the same
  limit and modulus.  Native and axiom-free; chains signed convergence (and hence
  signed-order-transitivity plus its D63 nnrat toolkit)."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.signed.convergence :as convergence]))

(def signed (function/const* 'signed/SignedRational []))
(def nat (function/const* 'data/Nat []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- addmono [a ah b bh ha hb]
  (app (function/const* 'nnrat/add-monotone []) a ah b bh ha hb))
(defn- fr [a b c d] (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- addcomm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- addresp [l le r re sl sr]
  (app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- atresp [l el r er sl sr ord]
  (app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- addcancel [x k y h]
  (app (function/const* 'nnrat/at-most-add-right-cancel []) x k y h))
(defn- eq-to-le [l r same]
  (app (function/const* 'nnrat/equivalent-to-at-most []) l r same))
(defn- etrans [x y z p q]
  (app (function/const* 'nnrat/equivalent-transitive []) x y z p q))
(defn- esym [x y p]
  (app (function/const* 'nnrat/equivalent-symmetric []) x y p))
(defn- erefl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- signed-erefl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-atresp [a ah b bh ea eb ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh ea eb ordered))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))
(defn- conjunction [l r]
  (app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r pl pr]
  (app (function/const* 'proposition/conjoin []) l r pl pr))
(defn- prop-left [l r both]
  (app (function/const* 'proposition/left []) l r both))
(defn- prop-right [l r both]
  (app (function/const* 'proposition/right []) l r both))

(def at-most-respects-equivalence-spec
  {:name 'signed/at-most-respects-equivalence :universes []
   :type
   (function/forall
    [['a signed] ['ah signed] ['b signed] ['bh signed]
     ['a-eq (seq-equiv 'a 'ah)]
     ['b-eq (seq-equiv 'b 'bh)]
     ['ordered (sle 'a 'b)]]
    (sle 'ah 'bh))
   :value
   (function/lam
    [['a signed] ['ah signed] ['b signed] ['bh signed]
     ['a-eq (seq-equiv 'a 'ah)]
     ['b-eq (seq-equiv 'b 'bh)]
     ['ordered (sle 'a 'b)]]
    (let [Pa (pos 'a) Na (neg 'a) Pah (pos 'ah) Nah (neg 'ah)
          Pb (pos 'b) Nb (neg 'b) Pbh (pos 'bh) Nbh (neg 'bh)

          ;; a-eq : Pa+Nah ~ Pah+Na.  Reverse it, add it to a<=b, isolate
          ;; the shared Pa+Na summand, and cancel to obtain ah<=b.
          a-back (eq-to-le
                  (radd Pah Na) (radd Pa Nah)
                  (esym (radd Pa Nah) (radd Pah Na) 'a-eq))
          a-sum (addmono (radd Pa Nb) (radd Pb Na)
                         (radd Pah Na) (radd Pa Nah)
                         'ordered a-back)
          a-left-eq
          (etrans
           (radd (radd Pah Nb) (radd Pa Na))
           (radd (radd Pah Pa) (radd Nb Na))
           (radd (radd Pa Nb) (radd Pah Na))
           (fr Pah Nb Pa Na)
           (etrans
            (radd (radd Pah Pa) (radd Nb Na))
            (radd (radd Pa Pah) (radd Nb Na))
            (radd (radd Pa Nb) (radd Pah Na))
            (addresp (radd Pah Pa) (radd Pa Pah)
                     (radd Nb Na) (radd Nb Na)
                     (addcomm Pah Pa) (erefl (radd Nb Na)))
            (esym (radd (radd Pa Nb) (radd Pah Na))
                  (radd (radd Pa Pah) (radd Nb Na))
                  (fr Pa Nb Pah Na))))
          a-right-eq
          (etrans
           (radd (radd Pb Nah) (radd Pa Na))
           (radd (radd Pb Pa) (radd Nah Na))
           (radd (radd Pb Na) (radd Pa Nah))
           (fr Pb Nah Pa Na)
           (etrans
            (radd (radd Pb Pa) (radd Nah Na))
            (radd (radd Pb Pa) (radd Na Nah))
            (radd (radd Pb Na) (radd Pa Nah))
            (addresp (radd Pb Pa) (radd Pb Pa)
                     (radd Nah Na) (radd Na Nah)
                     (erefl (radd Pb Pa)) (addcomm Nah Na))
            (esym (radd (radd Pb Na) (radd Pa Nah))
                  (radd (radd Pb Pa) (radd Na Nah))
                  (fr Pb Na Pa Nah))))
          a-transported
          (atresp (radd (radd Pah Nb) (radd Pa Na))
                  (radd (radd Pa Nb) (radd Pah Na))
                  (radd (radd Pb Nah) (radd Pa Na))
                  (radd (radd Pb Na) (radd Pa Nah))
                  a-left-eq a-right-eq a-sum)
          ah<=b (addcancel (radd Pah Nb) (radd Pa Na)
                           (radd Pb Nah) a-transported)

          ;; b-eq : Pb+Nbh ~ Pbh+Nb.  Add it to ah<=b, isolate the shared
          ;; Pb+Nb summand, and cancel to obtain ah<=bh.
          b-forward (eq-to-le (radd Pb Nbh) (radd Pbh Nb) 'b-eq)
          b-sum (addmono (radd Pah Nb) (radd Pb Nah)
                         (radd Pb Nbh) (radd Pbh Nb)
                         ah<=b b-forward)
          b-left-eq
          (etrans
           (radd (radd Pah Nbh) (radd Pb Nb))
           (radd (radd Pah Pb) (radd Nbh Nb))
           (radd (radd Pah Nb) (radd Pb Nbh))
           (fr Pah Nbh Pb Nb)
           (etrans
            (radd (radd Pah Pb) (radd Nbh Nb))
            (radd (radd Pah Pb) (radd Nb Nbh))
            (radd (radd Pah Nb) (radd Pb Nbh))
            (addresp (radd Pah Pb) (radd Pah Pb)
                     (radd Nbh Nb) (radd Nb Nbh)
                     (erefl (radd Pah Pb)) (addcomm Nbh Nb))
            (esym (radd (radd Pah Nb) (radd Pb Nbh))
                  (radd (radd Pah Pb) (radd Nb Nbh))
                  (fr Pah Nb Pb Nbh))))
          b-right-eq
          (etrans
           (radd (radd Pbh Nah) (radd Pb Nb))
           (radd (radd Pbh Pb) (radd Nah Nb))
           (radd (radd Pb Nah) (radd Pbh Nb))
           (fr Pbh Nah Pb Nb)
           (etrans
            (radd (radd Pbh Pb) (radd Nah Nb))
            (radd (radd Pb Pbh) (radd Nah Nb))
            (radd (radd Pb Nah) (radd Pbh Nb))
            (addresp (radd Pbh Pb) (radd Pb Pbh)
                     (radd Nah Nb) (radd Nah Nb)
                     (addcomm Pbh Pb) (erefl (radd Nah Nb)))
            (esym (radd (radd Pb Nah) (radd Pbh Nb))
                  (radd (radd Pb Pbh) (radd Nah Nb))
                  (fr Pb Nah Pbh Nb))))
          b-transported
          (atresp (radd (radd Pah Nbh) (radd Pb Nb))
                  (radd (radd Pah Nb) (radd Pb Nbh))
                  (radd (radd Pbh Nah) (radd Pb Nb))
                  (radd (radd Pb Nah) (radd Pbh Nb))
                  b-left-eq b-right-eq b-sum)]
      (addcancel (radd Pah Nbh) (radd Pb Nb)
                 (radd Pbh Nah) b-transported)))} )

(def converges-respects-pointwise-equivalence-spec
  {:name 'analysis/converges-respects-pointwise-equivalence :universes []
   :type
   (function/forall
    [['s sig-seq] ['t sig-seq] ['L signed] ['M modulus]
     ['pointwise
      (function/forall
       [['n nat]]
       (seq-equiv (app 's 'n) (app 't 'n)))]
     ['s-converges (converges 's 'L 'M)]]
    (converges 't 'L 'M))
   :value
   (function/lam
    [['s sig-seq] ['t sig-seq] ['L signed] ['M modulus]
     ['pointwise
      (function/forall
       [['n nat]]
       (seq-equiv (app 's 'n) (app 't 'n)))]
     ['s-converges (converges 's 'L 'M)]]
    (function/lam
     [['eps signed] ['n nat]
      ['large-enough (nat-at-most (app 'M 'eps) 'n)]]
     (let [sn (app 's 'n) tn (app 't 'n)
           lo (ssub 'L 'eps) hi (sadd 'L 'eps)
           close-s (app 's-converges 'eps 'n 'large-enough)
           lo<=sn (prop-left (sle lo sn) (sle sn hi) close-s)
           sn<=hi (prop-right (sle lo sn) (sle sn hi) close-s)
           sn-eq-tn (app 'pointwise 'n)
           lo<=tn (signed-atresp lo lo sn tn
                                 (signed-erefl lo) sn-eq-tn lo<=sn)
           tn<=hi (signed-atresp sn tn hi hi
                                 sn-eq-tn (signed-erefl hi) sn<=hi)]
       (conjoin (sle lo tn) (sle tn hi) lo<=tn tn<=hi))))})

(def definition-specs [])
(def theorem-specs
  [at-most-respects-equivalence-spec
   converges-respects-pointwise-equivalence-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convergence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-order-respects (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.order-respects))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
