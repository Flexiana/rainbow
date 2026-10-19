(ns rainbow.math.sums.binary-mutuality
  "Mutual selected-edge implications identify binary entries."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call at eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.boolean-predicate :as bits]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def mutuality-spec
  (let [x 'x y 'y X0 (eqv x s/zero) X1 (eqv x b/one) Y0 (eqv y s/zero) Y1 (eqv y b/one) goal (eqv x y)]
    (s/spec 'signed/binary-mutual-selection-implies-equivalence
      [[x signed] [y signed] ['xb (bits/binary x)] ['yb (bits/binary y)]
       ['forward (f/arrow X1 Y1)] ['reverse (f/arrow Y1 X1)]] goal
      (a/cases X0 X1 goal 'xb
        (f/lam [['xzero X0]]
          (a/cases Y0 Y1 goal 'yb
            (f/lam [['yzero Y0]] (s/trans x s/zero y 'xzero (s/sym y s/zero 'yzero)))
            (f/lam [['yone Y1]]
              (call 'proposition/explode goal (call 'signed/one-not-at-most-zero
                (a/eq-le b/one s/zero (s/trans b/one x s/zero (s/sym x b/one (at 'reverse 'yone)) 'xzero)))))))
        (f/lam [['xone X1]] (s/trans x b/one y 'xone (s/sym y b/one (at 'forward 'xone))))))))
(def theorem-specs [mutuality-spec])
(def deps '[rainbow.math.sums.binary-conflicts])
(defn install [env] (support/extend-with env :expr-sum-binary-mutuality theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.binary-mutuality))
