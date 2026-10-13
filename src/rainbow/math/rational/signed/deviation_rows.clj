(ns rainbow.math.rational.signed.deviation-rows
  "The two-row encoding of a magnitude bound says exactly what it looks like.

  A contract model says \"the deviation must stay within t\". A linear model
  cannot write a magnitude, so it writes two rows,

      d <= t     and     -d <= t,

  and the question a verified reformulation has to answer is whether that pair is
  the same constraint. Unlike the indicator row, this one admits a full
  EQUIVALENCE rather than a pair of one-way guarantees:

    optimization/deviation-rows-sound
      d <= t  ->  -d <= t  ->  max(d, -d) <= t
      the two rows are enough: nothing outside the magnitude bound survives them;

    optimization/deviation-rows-complete
      max(d, -d) <= t  ->  (d <= t) AND (-d <= t)
      the two rows are not too many: everything the magnitude bound allowed
      still satisfies both.

  Together they say the encoding is neither too tight nor too loose, which is the
  strongest form of reformulation guarantee and the one a buyer should ask for
  before trusting a model they did not write.

  `signed/max` and its bound laws come from the signed lattice; this module only
  adds the `optimization/` statements that connect them to the modelling
  question. `signed/negate-reverses-order` is proved here because the order cone
  is where it belongs: negating both sides of a comparison swaps the two
  Grothendieck cross sums, so it is additive commutativity transported through
  the nnrat order.

  Native and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.order-transitivity :as transitivity]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sneg [v] (app (function/const* 'signed/negate []) v))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))

(defn- rat-comm [a b] (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))

;; a <= b  gives  -b <= -a. Unfolded the premise is Pa + Nb <= Pb + Na and the
;; conclusion is Nb + Pa <= Na + Pb: the same comparison with each side commuted.
(def negate-reverses-order-spec
  {:name 'signed/negate-reverses-order :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['ordered (sle 'a 'b)]]
          (sle (sneg 'b) (sneg 'a)))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ordered (sle 'a 'b)]]
    (let [Pa (pos 'a) Na (neg 'a) Pb (pos 'b) Nb (neg 'b)]
      (rat-at-most-respects
       (radd Nb Pa) (radd Pa Nb)
       (radd Na Pb) (radd Pb Na)
       (rat-comm Nb Pa) (rat-comm Na Pb)
       'ordered)))})

(def deviation-rows-sound-spec
  {:name 'optimization/deviation-rows-sound :universes []
   :type (function/forall
          [['d signed] ['t signed]
           ['above (sle 'd 't)]
           ['below (sle (sneg 'd) 't)]]
          (sle (smax 'd (sneg 'd)) 't))
   :value
   (function/lam
    [['d signed] ['t signed]
     ['above (sle 'd 't)]
     ['below (sle (sneg 'd) 't)]]
    (app (function/const* 'signed/at-most-max [])
         'd (sneg 'd) 't 'above 'below))})

(def deviation-rows-complete-spec
  {:name 'optimization/deviation-rows-complete :universes []
   :type (function/forall
          [['d signed] ['t signed]
           ['bounded (sle (smax 'd (sneg 'd)) 't)]]
          (conjunction (sle 'd 't) (sle (sneg 'd) 't)))
   :value
   (function/lam
    [['d signed] ['t signed]
     ['bounded (sle (smax 'd (sneg 'd)) 't)]]
    (conjoin
     (sle 'd 't) (sle (sneg 'd) 't)
     (signed-transitive 'd (smax 'd (sneg 'd)) 't
                        (app (function/const* 'signed/max-upper-left [])
                             'd (sneg 'd))
                        'bounded)
     (signed-transitive (sneg 'd) (smax 'd (sneg 'd)) 't
                        (app (function/const* 'signed/max-upper-right [])
                             'd (sneg 'd))
                        'bounded)))})

(def definition-specs [])
(def theorem-specs
  [negate-reverses-order-spec
   deviation-rows-sound-spec
   deviation-rows-complete-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-monotone/extend-environment
      transitivity/extend-environment
      minmax/extend-environment
      (support/extend-with :signed-deviation-rows theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
