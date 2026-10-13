(ns rainbow.math.rational.signed.order-cancellation
  "Additive cancellation for signed-rational order.

      a + c <= b + c  ==>  a <= b
      c + a <= c + b  ==>  a <= b

  These are the converses of `signed/add-right-monotone` / `-left-monotone`, and
  the missing half of the additive order toolkit: monotonicity lets a shared
  summand be introduced, cancellation lets it be removed.  Removing a shared
  summand is what turns an inequality between Lagrangian values into an
  inequality between the penalty terms, so this is the lemma that unlocks
  complementary-slackness style arguments over signed rationals.

  Signed order `u <= v` unfolds to the nnrat order

      positive u + negative v  <=  positive v + negative u,

  so both statements reduce to isolating the shared `positive c + negative c`
  summand and discharging it with `nnrat/at-most-add-right-cancel`.  The two
  isolations are pure semiring reorderings, so each is a single
  `rainbow.math.rational.nnrat.ring` call.  Native and axiom-free; chains the D63 signed
  order transitivity toolkit and the nnrat-ring tactic."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.order-transitivity :as st]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))

(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- rat-add-right-cancel [x k y ordered]
  (app (function/const* 'nnrat/at-most-add-right-cancel []) x k y ordered))

;; a + c <= b + c  ==>  a <= b
;;
;; Unfolded the premise is (Pa+Pc)+(Nb+Nc) <= (Pb+Pc)+(Na+Nc).  Normalizing
;; rewrites both sides into the shape (goal side)+(Pc+Nc), which the nnrat right
;; cancellation strips.
(def add-right-cancel-spec
  {:name 'signed/at-most-add-right-cancel :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['ordered (sle (sadd 'a 'c) (sadd 'b 'c))]]
          (sle 'a 'b))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['ordered (sle (sadd 'a 'c) (sadd 'b 'c))]]
    (let [Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          Pc (pos 'c) Nc (neg 'c)
          shared (radd Pc Nc)
          goal-left (radd Pa Nb)
          goal-right (radd Pb Na)
          padded-left (radd goal-left shared)
          padded-right (radd goal-right shared)
          raw-left (radd (radd Pa Pc) (radd Nb Nc))
          raw-right (radd (radd Pb Pc) (radd Na Nc))
          padded
          (rat-at-most-respects padded-left raw-left padded-right raw-right
                                (ring/equiv padded-left raw-left)
                                (ring/equiv padded-right raw-right)
                                'ordered)]
      (rat-add-right-cancel goal-left shared goal-right padded)))})

;; c + a <= c + b  ==>  a <= b
;;
;; Same shape, with the premise now reading (Pc+Pa)+(Nc+Nb) <= (Pc+Pb)+(Nc+Na).
(def add-left-cancel-spec
  {:name 'signed/at-most-add-left-cancel :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['ordered (sle (sadd 'c 'a) (sadd 'c 'b))]]
          (sle 'a 'b))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['ordered (sle (sadd 'c 'a) (sadd 'c 'b))]]
    (let [Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          Pc (pos 'c) Nc (neg 'c)
          shared (radd Pc Nc)
          goal-left (radd Pa Nb)
          goal-right (radd Pb Na)
          padded-left (radd goal-left shared)
          padded-right (radd goal-right shared)
          raw-left (radd (radd Pc Pa) (radd Nc Nb))
          raw-right (radd (radd Pc Pb) (radd Nc Na))
          padded
          (rat-at-most-respects padded-left raw-left padded-right raw-right
                                (ring/equiv padded-left raw-left)
                                (ring/equiv padded-right raw-right)
                                'ordered)]
      (rat-add-right-cancel goal-left shared goal-right padded)))})

(def definition-specs [])
(def theorem-specs [add-right-cancel-spec add-left-cancel-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      st/extend-environment
      ring/extend-environment
      (support/extend-with :signed-order-cancellation theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
