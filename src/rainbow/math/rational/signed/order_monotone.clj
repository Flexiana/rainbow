(ns rainbow.math.rational.signed.order-monotone
  "Real-analysis roadmap step 6a: signed order is monotone under addition --

    signed/add-right-monotone : a <= b -> (a + c) <= (b + c)

  signed/add adds pos/neg componentwise (pos(a+c) = pos a + pos c, etc. -- reduces
  definitionally, since signed/positive-of-make is reflexivity), so the goal
    (Pa+Pc)+(Nb+Nc) <= (Pb+Pc)+(Na+Nc)
  reorders (nnrat/add-four-reorder) to
    (Pa+Nb)+(Pc+Nc) <= (Pb+Na)+(Pc+Nc)
  which is nnrat/add-monotone applied to the hypothesis Pa+Nb <= Pb+Na with the common
  (Pc+Nc) (at-most-reflexive), transported back by nnrat/at-most-respects-equivalence.

  A building block for 'L <= L + eps' and the limit laws.  Native and axiom-free; chains
  rainbow.math.rational.signed.order-transitivity (-> nnrat add-monotone, four-reorder) on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.signed.order-transitivity :as st]))

(def signed (function/const* 'signed/SignedRational []))

(defn- pos [v] (function/app (function/const* 'signed/positive []) v))
(defn- neg [v] (function/app (function/const* 'signed/negative []) v))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (function/app (function/const* 'signed/add []) a b))
(defn- sle [a b] (function/app (function/const* 'signed/at-most []) a b))
(defn- addmono [a ah b bh ha hb]
  (function/app (function/const* 'nnrat/add-monotone []) a ah b bh ha hb))
(defn- fr [a b c d] (function/app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- atresp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- rat-refl [v] (function/app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- signed-transitive [l m r p q]
  (function/app (function/const* 'signed/at-most-transitive []) l m r p q))

(def add-right-monotone-spec
  {:name 'signed/add-right-monotone :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['ha (sle 'a 'b)]]
          (sle (sadd 'a 'c) (sadd 'b 'c)))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['ha (sle 'a 'b)]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b) Pc (pos 'c) Nc (neg 'c)
          core (addmono (radd Pa Nb) (radd Pb Na) (radd Pc Nc) (radd Pc Nc)
                        'ha (rat-refl (radd Pc Nc)))    ; (Pa+Nb)+(Pc+Nc) <= (Pb+Na)+(Pc+Nc)
          e-left (fr Pa Pc Nb Nc)      ; (Pa+Pc)+(Nb+Nc) ~ (Pa+Nb)+(Pc+Nc)
          e-right (fr Pb Pc Na Nc)]    ; (Pb+Pc)+(Na+Nc) ~ (Pb+Na)+(Pc+Nc)
      (atresp (radd (radd Pa Pc) (radd Nb Nc)) (radd (radd Pa Nb) (radd Pc Nc))
              (radd (radd Pb Pc) (radd Na Nc)) (radd (radd Pb Na) (radd Pc Nc))
              e-left e-right core)))})

;; c + a <= c + b  (left addend fixed)
(def add-left-monotone-spec
  {:name 'signed/add-left-monotone :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['ha (sle 'a 'b)]]
          (sle (sadd 'c 'a) (sadd 'c 'b)))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['ha (sle 'a 'b)]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b) Pc (pos 'c) Nc (neg 'c)
          core (addmono (radd Pc Nc) (radd Pc Nc) (radd Pa Nb) (radd Pb Na)
                        (rat-refl (radd Pc Nc)) 'ha)   ; (Pc+Nc)+(Pa+Nb) <= (Pc+Nc)+(Pb+Na)
          e-left (fr Pc Pa Nc Nb)    ; (Pc+Pa)+(Nc+Nb) ~ (Pc+Nc)+(Pa+Nb)
          e-right (fr Pc Pb Nc Na)]  ; (Pc+Pb)+(Nc+Na) ~ (Pc+Nc)+(Pb+Na)
      (atresp (radd (radd Pc Pa) (radd Nc Nb)) (radd (radd Pc Nc) (radd Pa Nb))
              (radd (radd Pc Pb) (radd Nc Na)) (radd (radd Pc Nc) (radd Pb Na))
              e-left e-right core)))})

;; two-sided: a<=a' -> b<=b' -> (a+b) <= (a'+b')
(def add-monotone-spec
  {:name 'signed/add-monotone :universes []
   :type (function/forall
          [['a signed] ['ah signed] ['b signed] ['bh signed]
           ['ha (sle 'a 'ah)] ['hb (sle 'b 'bh)]]
          (sle (sadd 'a 'b) (sadd 'ah 'bh)))
   :value
   (function/lam
    [['a signed] ['ah signed] ['b signed] ['bh signed]
     ['ha (sle 'a 'ah)] ['hb (sle 'b 'bh)]]
    (signed-transitive
     (sadd 'a 'b) (sadd 'ah 'b) (sadd 'ah 'bh)
     (function/app (function/const* 'signed/add-right-monotone []) 'a 'ah 'b 'ha)
     (function/app (function/const* 'signed/add-left-monotone []) 'b 'bh 'ah 'hb)))})

(def definition-specs [])
(def theorem-specs [add-right-monotone-spec add-left-monotone-spec add-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      st/extend-environment
      (support/extend-with :signed-order-monotone
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
