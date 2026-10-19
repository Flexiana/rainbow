(ns rainbow.math.sums.one-hot-index
  "Every selected index reads every one-hot weighted sum; every distinct index is zero."
  (:require [rainbow.math.logic.function :as f] [rainbow.math.logic.proposition :as prop]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum eqv le refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.flow-cut :as a] [rainbow.math.sums.binary-conflicts :as binary]
            [rainbow.math.sums.boolean-predicate :as bits]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def U [:succ [:zero]])
(defn eqnat [x y] (f/equality U nat x y))
(defn notp [P] (call 'proposition/negation P))
(defn nn [W n binary-proof]
  (let [i (gensym "index") h (gensym "bound")]
    (f/lam [[i nat] [h (s/below i n)]] (call 'signed/boolean-cases-nonnegative (at W i) (at binary-proof i h)))))
(defn binary-on [W n] (s/all-below n #(bits/binary (at W %))))
(defn selection-parts [W n p]
  (let [X (gensym "values")]
    [(s/below p n) (eqv (at W p) b/one) (f/forall [[X family]] (eqv (lp/objective W X n) (at X p)))]))
(def read-spec
  (let [W 'W F 'F n 'n w 'w goal (eqv (lp/objective W F n) (at F w))
        nonnegative (nn W n 'binary)]
    (s/spec 'signed/one-hot-selected-index-reads
      [[W family] [F family] [n nat] ['binary (binary-on W n)] ['unit (eqv (sum W n) b/one)]
       [w nat] ['bound (s/below w n)] ['selected (eqv (at W w) b/one)]] goal
      (at (call 'signed/one-hot-selects W n nonnegative 'binary 'unit) goal
        (f/lam [['p nat] ['witness (b/conjunction (selection-parts W n 'p))]]
          (let [ps (selection-parts W n 'p) hp (b/extract ps 0 'witness) sp (b/extract ps 1 'witness)
                reads (b/extract ps 2 'witness)
                equal (call 'signed/one-hot-unique W n nonnegative 'unit 'p w hp 'bound sp 'selected)]
            (a/nsubst 'p w equal (f/lam [['index nat]] (eqv (lp/objective W F n) (at F 'index))) (at reads F))))))))
(def other-zero-spec
  (let [W 'W n 'n w 'w j 'j P (eqv (at W j) s/zero) Q (eqv (at W j) b/one)]
    (s/spec 'signed/one-hot-distinct-index-zero
      [[W family] [n nat] ['binary (binary-on W n)] ['unit (eqv (sum W n) b/one)]
       [w nat] ['hw (s/below w n)] ['selected (eqv (at W w) b/one)]
       [j nat] ['hj (s/below j n)] ['distinct (notp (eqnat w j))]] P
      (a/cases P Q P (at 'binary j 'hj)
        (f/lam [['zero P]] 'zero)
        (f/lam [['one Q]] (call 'proposition/explode P
                           (at 'distinct (call 'signed/one-hot-unique W n (nn W n 'binary) 'unit w j 'hw 'hj 'selected 'one))))))))
(def zero-distinct-spec
  (let [W 'W w 'w j 'j]
    (s/spec 'signed/one-and-zero-indices-distinct
      [[W family] [w nat] [j nat] ['one (eqv (at W w) b/one)] ['zero (eqv (at W j) s/zero)]]
      (notp (eqnat w j))
      (f/lam [['equal (eqnat w j)]]
        (let [jone (a/nsubst w j 'equal (f/lam [['index nat]] (eqv (at W 'index) b/one)) 'one)]
          (call 'signed/one-not-at-most-zero
            (a/eq-le b/one s/zero (s/trans b/one (at W j) s/zero (s/sym (at W j) b/one jone) 'zero))))))))
(def theorem-specs [read-spec other-zero-spec zero-distinct-spec])
(def deps '[rainbow.math.sums.binary-conflicts rainbow.math.rational.signed.one-hot-selects rainbow.math.rational.signed.one-hot-unique])
(defn install [env] (support/extend-with env :expr-sum-one-hot-index theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.one-hot-index))
