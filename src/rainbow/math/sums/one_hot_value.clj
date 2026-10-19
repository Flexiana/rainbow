(ns rainbow.math.sums.one-hot-value
  "Pointwise values of a selected index, their weighted equality, and explicit attainment."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum eqv]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.one-hot-index :as hot]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(defn selected-values [W F V n]
  (let [i (gensym "selected-index") hi (gensym "bound") selected (gensym "selected")]
    (f/forall [[i nat] [hi (s/below i n)] [selected (eqv (at W i) b/one)]] (eqv V (at F i)))))
(defn exists-index [F V n]
  (f/app (f/const* 'proposition/existence [hot/U]) nat
    (f/lam [['index nat]] (b/conjunction [(s/below 'index n) (eqv (at F 'index) V)]))))
(def forward-spec
  (s/spec 'signed/one-hot-value-implies-selected-values
    [['W family] ['F family] ['V signed] ['n nat] ['binary (hot/binary-on 'W 'n)] ['unit (eqv (sum 'W 'n) b/one)]
     ['value (eqv 'V (lp/objective 'W 'F 'n))]] (selected-values 'W 'F 'V 'n)
    (f/lam [['i nat] ['hi (s/below 'i 'n)] ['selected (eqv (at 'W 'i) b/one)]]
      (s/trans 'V (lp/objective 'W 'F 'n) (at 'F 'i) 'value
        (call 'signed/one-hot-selected-index-reads 'W 'F 'n 'binary 'unit 'i 'hi 'selected)))))
(defn select [W n binary unit goal body]
  (let [i (gensym "selected-index") h (gensym "witness") ps (hot/selection-parts W n i)]
    (at (call 'signed/one-hot-selects W n (hot/nn W n binary) binary unit) goal
      (f/lam [[i nat] [h (b/conjunction ps)]]
        (body i (b/extract ps 0 h) (b/extract ps 1 h) (b/extract ps 2 h))))))
(def backward-spec
  (s/spec 'signed/selected-values-imply-one-hot-value
    [['W family] ['F family] ['V signed] ['n nat] ['binary (hot/binary-on 'W 'n)] ['unit (eqv (sum 'W 'n) b/one)]
     ['values (selected-values 'W 'F 'V 'n)]] (eqv 'V (lp/objective 'W 'F 'n))
    (select 'W 'n 'binary 'unit (eqv 'V (lp/objective 'W 'F 'n))
      (fn [i hi selected reads]
        (s/trans 'V (at 'F i) (lp/objective 'W 'F 'n) (at 'values i hi selected)
          (s/sym (lp/objective 'W 'F 'n) (at 'F i) (at reads 'F)))))))
(def attained-spec
  (s/spec 'signed/one-hot-value-is-attained
    [['W family] ['F family] ['V signed] ['n nat] ['binary (hot/binary-on 'W 'n)] ['unit (eqv (sum 'W 'n) b/one)]
     ['value (eqv 'V (lp/objective 'W 'F 'n))]] (exists-index 'F 'V 'n)
    (select 'W 'n 'binary 'unit (exists-index 'F 'V 'n)
      (fn [i hi selected reads]
        (f/app (f/const* 'proposition/witness [hot/U]) nat
          (f/lam [['index nat]] (b/conjunction [(s/below 'index 'n) (eqv (at 'F 'index) 'V)])) i
          (b/conjoin [(s/below i 'n) (eqv (at 'F i) 'V)]
            [hi (s/sym 'V (at 'F i) (s/trans 'V (lp/objective 'W 'F 'n) (at 'F i) 'value (at reads 'F)))]))))))
(def theorem-specs [forward-spec backward-spec attained-spec])
(def deps '[rainbow.math.sums.one-hot-index])
(defn install [env] (support/extend-with env :expr-sum-one-hot-value theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.one-hot-value))
