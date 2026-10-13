(ns rainbow.math.rational.nnrat.complement-proper
  "Proper raw fraction for the exact complement of a positive subunit mass."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ordered-distance :as ordered]
            [rainbow.math.rational.nnrat.positive :as positive]
            [rainbow.math.nat.add-order :as add-order]))

(def level [:succ [:zero]])
(def nat (f/const* 'data/Nat []))
(def rat (f/const* 'nnrat/NonnegativeRational []))
(def zero (f/const* 'data/zero []))
(def one (f/const* 'nnrat/one []))
(defn- app [name & xs] (apply f/app (f/const* name []) xs))
(defn- succ [x] (app 'data/succ x))
(def none (succ zero))
(defn- add [a b] (app 'algebra/nat-add a b))
(defn- mul [a b] (app 'nat/multiply a b))
(defn- dist [a b] (app 'nat/distance a b))
(defn- le [a b] (app 'nat/at-most a b))
(defn- eqn [a b] (f/equality level nat a b))
(defn- sym [a b proof] (f/app (f/const* 'equality/symmetric [level]) nat a b proof))
(defn- trans [a b c p q] (f/app (f/const* 'equality/transitive [level]) nat a b c p q))
(defn- cong [mapping a b proof]
  (f/app (f/const* 'equality/congruent-function [level level]) nat nat mapping a b proof))
(defn proper [r]
  (le (app 'nnrat/numerator r) (app 'nnrat/denominator-predecessor r)))

(def distance-upper-of-ordered-spec
  (let [bindings [['left nat] ['right nat] ['ordered (le 'left 'right)]]
        d (dist 'left 'right) padded (add d 'left) reconstructed (add 'left d)]
    {:name 'nat/distance-at-most-upper-of-at-most :universes []
     :type (f/forall bindings (le d 'right))
     :value (f/lam bindings
              (app 'nat/at-most-rewrite-right d padded 'right
                (trans padded reconstructed 'right
                  (app 'nat/add-commutative d 'left)
                  (app 'nat/add-distance-of-at-most 'left 'right 'ordered))
                (app 'nat/le-add-right d 'left)))}))

(def complement-proper-spec
  (let [rho (app 'nnrat/distance 'value one)
        n (app 'nnrat/numerator 'value) dp (app 'nnrat/denominator-predecessor 'value)
        d (succ dp) a (mul n none) b (mul none d)
        bindings [['value rat] ['bounded (app 'nnrat/at-most 'value one)]
                  ['positive (app 'nnrat/positive 'value)]]
        goal (proper rho)
        witness-predicate (f/lam [['np nat]] (eqn (add none 'np) n))]
    {:name 'nnrat/distance-to-one-proper-of-positive-at-most-one :universes []
     :type (f/forall bindings goal)
     :value
     (f/lam bindings
       (f/app (f/const* 'proposition/use-witness [level]) nat witness-predicate goal 'positive
         (f/lam [['np nat] ['numerator-is-successor (eqn (add none 'np) n)]]
           (let [sn (succ 'np)
                 a-is-sn (trans a n sn (app 'nat/multiply-one-right n)
                           (sym sn n 'numerator-is-successor))
                 b-is-d (app 'algebra/nat-add-zero-right d)
                 cross (app 'nnrat/at-most-to-cross 'value one 'bounded)
                 sn-b (app 'nat/at-most-rewrite-left sn a b (sym a sn a-is-sn) cross)
                 sn-d (app 'nat/at-most-rewrite-right sn b d b-is-d sn-b)
                 np-dp (app 'nat/at-most-add-left-cancel 'np dp none sn-d)
                 small-distance (dist 'np dp)
                 small-bound (app 'nat/distance-at-most-upper-of-at-most 'np dp np-dp)
                 raw-distance (dist a b)
                 same-distance
                 (trans raw-distance (dist sn b) (dist sn d)
                   (cong (f/lam [['candidate nat]] (dist 'candidate b)) a sn a-is-sn)
                   (cong (f/lam [['candidate nat]] (dist sn 'candidate)) b d b-is-d))
                 raw-bound (app 'nat/at-most-rewrite-left raw-distance small-distance dp
                             same-distance small-bound)
                 packed-dp (app 'nnrat/denominator-predecessor rho)
                 packed-is-dp
                 (cong (f/lam [['candidate nat]] (app 'nat/predecessor 'candidate))
                       (mul d none) d (app 'nat/multiply-one-right d))]
             (app 'nat/at-most-rewrite-right raw-distance dp packed-dp
                  (sym packed-dp dp packed-is-dp) raw-bound)))))}))

(def theorem-specs [distance-upper-of-ordered-spec complement-proper-spec])
(defn extend-environment [env]
  (-> env ordered/extend-environment positive/extend-environment add-order/extend-environment
      (support/extend-with :nnrat-complement-proper theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
