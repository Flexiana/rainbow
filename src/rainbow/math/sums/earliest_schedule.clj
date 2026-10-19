(ns rainbow.math.sums.earliest-schedule
  "The earliest-start recurrence preserves feasibility whenever any window schedule exists."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at add le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonblocking :as nb] [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def max-left-spec
  (s/spec 'signed/maximum-at-least-left [['x signed] ['y signed]] (le 'x (nb/maximum 'x 'y))
    (#'cea/by-bit (cea/dec 'x 'y) #(le 'x (nb/max-bit 'x 'y %))
      (fn [_] (call 'signed/at-most-reflexive 'x))
      (fn [h] (call 'signed/decide-at-most-true-sound 'x 'y h)) 'decision)))
(def max-right-spec
  (s/spec 'signed/maximum-at-least-right [['x signed] ['y signed]] (le 'y (nb/maximum 'x 'y))
    (#'cea/by-bit (cea/dec 'x 'y) #(le 'y (nb/max-bit 'x 'y %))
      (fn [h] (call 'signed/decide-at-most-false-reverse 'x 'y h))
      (fn [_] (call 'signed/at-most-reflexive 'y)) 'decision)))
(def max-upper-spec
  (s/spec 'signed/maximum-below-common-upper [['x signed] ['y signed] ['z signed] ['left (le 'x 'z)] ['right (le 'y 'z)]]
    (le (nb/maximum 'x 'y) 'z)
    (#'cea/by-bit (cea/dec 'x 'y) #(le (nb/max-bit 'x 'y %) 'z) (fn [_] 'left) (fn [_] 'right) 'decision)))
(def earliest-spec
  {:name 'signed/earliest-window-start :kind :definition :transparency :reducible :universes []
   :type (f/arrow family family nat signed)
   :value (f/lam [['A family] ['D family] ['k nat]]
            (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]]) (f/lam [['ignored nat]] signed) (at 'A s/nz)
              (f/lam [['previous nat] ['earlier signed]] (nb/maximum (at 'A (s/succ 'previous)) (add 'earlier (at 'D 'previous)))) 'k))})
(defn earliest [A D k] (call 'signed/earliest-window-start A D k))
(defn times [A D] (let [i (gensym "position")] (f/lam [[i nat]] (earliest A D i))))
(defn windows [A B D T q]
  [(s/all-below (s/succ q) #(le (at A %) (at T %)))
   (s/all-below (s/succ q) #(le (at T %) (at B %)))
   (s/all-below q #(le (add (at T %) (at D %)) (at T (s/succ %))))])
(defn induct [claim base step n]
  (let [k (gensym "period") p (gensym "previous") ih (gensym "hypothesis")]
    (f/app (f/const* 'data/Nat.rec [[:zero]]) (f/lam [[k nat]] (claim k)) base
      (f/lam [[p nat] [ih (claim p)]] (step p ih)) n)))
(def lower-spec
  (s/spec 'signed/earliest-start-above-opening [['A family] ['D family] ['k nat]]
    (le (at 'A 'k) (earliest 'A 'D 'k))
    (induct #(le (at 'A %) (earliest 'A 'D %)) (call 'signed/at-most-reflexive (at 'A s/nz))
      (fn [k _] (call 'signed/maximum-at-least-left (at 'A (s/succ k)) (add (earliest 'A 'D k) (at 'D k)))) 'k)))
(def least-spec
  (let [A 'A D 'D T 'T q 'q n (s/succ q) k 'k
        lower (s/all-below n #(le (at A %) (at T %)))
        progress (s/all-below q #(le (add (at T %) (at D %)) (at T (s/succ %))))
        claim (fn [i] (f/forall [['bound (s/below i n)]] (le (earliest A D i) (at T i))))]
    (s/spec 'signed/earliest-start-no-later-than-feasible
      [[A family] [D family] [T family] [q nat] ['lower lower] ['progress progress] [k nat]] (claim k)
      (induct claim (f/lam [['bound (s/below s/nz n)]] (at 'lower s/nz 'bound))
        (fn [i ih]
          (let [hi (call 'nat/at-most-successor-cancel-local (s/succ i) q 'bound)
                hin (s/weaken i q hi)
                arriving (a/le-trans (add (earliest A D i) (at D i)) (add (at T i) (at D i)) (at T (s/succ i))
                           (call 'signed/add-right-monotone (earliest A D i) (at T i) (at D i) (at ih hin))
                           (at 'progress i hi))]
            (f/lam [['bound (s/below (s/succ i) n)]]
              (call 'signed/maximum-below-common-upper (at A (s/succ i)) (add (earliest A D i) (at D i)) (at T (s/succ i))
                (at 'lower (s/succ i) 'bound) arriving)))) k))))
(def feasible-spec
  (let [A 'A B 'B D 'D T 'T q 'q ps (windows A B D T q) g #(b/extract ps % 'feasible) E (times A D)]
    (s/spec 'signed/earliest-start-preserves-feasibility
      [[A family] [B family] [D family] [T family] [q nat] ['feasible (b/conjunction ps)]]
      (b/conjunction (windows A B D E q))
      (b/conjoin (windows A B D E q)
        [(f/lam [['i nat] ['hi (s/below 'i (s/succ q))]] (call 'signed/earliest-start-above-opening A D 'i))
         (f/lam [['i nat] ['hi (s/below 'i (s/succ q))]]
           (a/le-trans (earliest A D 'i) (at T 'i) (at B 'i)
             (call 'signed/earliest-start-no-later-than-feasible A D T q (g 0) (g 2) 'i 'hi) (at (g 1) 'i 'hi)))
         (f/lam [['i nat] ['hi (s/below 'i q)]]
           (call 'signed/maximum-at-least-right (at A (s/succ 'i)) (add (earliest A D 'i) (at D 'i))))]))))
(def definition-specs [earliest-spec])
(def theorem-specs [max-left-spec max-right-spec max-upper-spec lower-spec least-spec feasible-spec])
(def deps '[rainbow.math.sums.nonblocking rainbow.math.nat.at-most-cancellation rainbow.algorithms.proofs.graph.walk-shorten])
(defn install [env] (support/extend-with env :expr-sum-earliest-schedule (concat definition-specs theorem-specs)))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.earliest-schedule))
