(ns rainbow.algorithms.proofs.ahof.epsilon-greedy
  "AHoF epsilon-greedy exploration: the canonical explore/exploit rule for
  bandits and reinforcement learning. With probability epsilon take a random
  (exploring) action; otherwise take the greedy action argmax_a Q(a). Given a
  uniform draw u in [0,1), the agent explores exactly when u falls in the
  epsilon-band:

      explores? u epsilon = decide (u <= epsilon)
      exploit-action Q    = argmax_a Q(a)

  over exact-rational epsilon and Q-values. Defined: the exploration test and
  the exploit action (via the argmax-index fold). Proved native and axiom-free, as
  worked instances: draw 1/10 with epsilon 1/4 explores, draw 1/2 with epsilon 1/4
  exploits, the worked certificate 1/10 <= 1/4 (native nnrat/at-most), and
  exploit-action [5,7,4] = 1. That the exploit action is the argmax for every Q,
  and the rule's classical regret behaviour, are not proved here. The Q
  estimates, the RNG, and the random action are executable.

  Requires argmax-index/argmax-index, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.epsilon-greedy`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- explores? [u epsilon]
  (function/app (function/const* 'epsilon-greedy/explores? []) u epsilon))
(defn- exploit-action [q]
  (function/app (function/const* 'epsilon-greedy/exploit-action []) q))
(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; explores? u epsilon = decide (u <= epsilon)
(def explores-spec
  {:name 'epsilon-greedy/explores? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['u nnrat] ['epsilon nnrat]]
                        (decide-at-most 'u 'epsilon))})

;; exploit-action Q = argmax_a Q(a)
(def exploit-action-spec
  {:name 'epsilon-greedy/exploit-action :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['q list-nnrat]] (argmax-index-app 'q))})

(def definition-specs [explores-spec exploit-action-spec])

;; Theorems -----------------------------------------------------------------

;; A draw of 1/10 with epsilon = 1/4 explores.
(def draw-explores-spec
  {:name 'epsilon-greedy/draw-explores :universes []
   :type (equality bool (explores? (fraction 1 9) (fraction 1 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (explores? (fraction 1 9) (fraction 1 3)))})

;; Worked certificate 1/10 <= 1/4.
(def exploration-in-band-spec
  {:name 'epsilon-greedy/exploration-in-band :universes []
   :type (nnrat-at-most (fraction 1 9) (fraction 1 3))
   :value (at-most-proof (fraction 1 9) (fraction 1 3))})

;; A draw of 1/2 (> epsilon 1/4) exploits.
(def draw-exploits-spec
  {:name 'epsilon-greedy/draw-exploits :universes []
   :type (equality bool (explores? (fraction 1 1) (fraction 1 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (explores? (fraction 1 1) (fraction 1 3)))})

;; Worked instance: exploit-action [5,7,4] = 1.
(def exploit-is-greedy-spec
  {:name 'epsilon-greedy/exploit-is-greedy :universes []
   :type (equality nat
                   (exploit-action (nnrat-list (whole 5) (whole 7) (whole 4)))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (exploit-action (nnrat-list (whole 5) (whole 7)
                                                    (whole 4))))})

(def theorem-specs
  [draw-explores-spec exploration-in-band-spec draw-exploits-spec
   exploit-is-greedy-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      argmax-index/extend-environment
      (support/extend-with :ahof-epsilon-greedy
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
