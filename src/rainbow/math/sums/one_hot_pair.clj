(ns rainbow.math.sums.one-hot-pair
  "Two independent one-hot rows select exactly the corresponding matrix entry."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum eqv]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.one-hot-index :as hot] [rainbow.math.sums.one-hot-value :as value]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def matrix (f/arrow nat family))
(defn inner [D Z n] (let [i (gensym "row")] (f/lam [[i nat]] (lp/objective Z (at D i) n))))
(defn bilinear [W Z D m n] (lp/objective W (inner D Z n) m))
(defn selected-values [W Z D V m n]
  (let [i (gensym "row") hi (gensym "bound") wi (gensym "selected") j (gensym "column") hj (gensym "bound") zj (gensym "selected")]
    (f/forall [[i nat] [hi (s/below i m)] [wi (eqv (at W i) b/one)] [j nat] [hj (s/below j n)] [zj (eqv (at Z j) b/one)]]
      (eqv V (at D i j)))))
(defn assumptions [W Z m n]
  [['wb (hot/binary-on W m)] ['wu (eqv (sum W m) b/one)] ['zb (hot/binary-on Z n)] ['zu (eqv (sum Z n) b/one)]])
(def forward-spec
  (let [W 'W Z 'Z D 'D V 'V m 'm n 'n I (inner D Z n) total (bilinear W Z D m n)]
    (s/spec 'signed/one-hot-bilinear-implies-selected-pair-values
      (into [[W family] [Z family] [D matrix] [V signed] [m nat] [n nat]]
        (concat (assumptions W Z m n) [['value (eqv V total)]]))
      (selected-values W Z D V m n)
      (f/lam [['i nat] ['hi (s/below 'i m)] ['wi (eqv (at W 'i) b/one)]
               ['j nat] ['hj (s/below 'j n)] ['zj (eqv (at Z 'j) b/one)]]
        (s/trans V total (at D 'i 'j) 'value
          (s/trans total (lp/objective Z (at D 'i) n) (at D 'i 'j)
            (call 'signed/one-hot-selected-index-reads W I m 'wb 'wu 'i 'hi 'wi)
            (call 'signed/one-hot-selected-index-reads Z (at D 'i) n 'zb 'zu 'j 'hj 'zj)))))))
(def backward-spec
  (let [W 'W Z 'Z D 'D V 'V m 'm n 'n I (inner D Z n) total (bilinear W Z D m n)]
    (s/spec 'signed/selected-pair-values-imply-one-hot-bilinear
      (into [[W family] [Z family] [D matrix] [V signed] [m nat] [n nat]]
        (concat (assumptions W Z m n) [['values (selected-values W Z D V m n)]]))
      (eqv V total)
      (value/select W m 'wb 'wu (eqv V total)
        (fn [i hi wi readi]
          (value/select Z n 'zb 'zu (eqv V total)
            (fn [j hj zj readj]
              (s/trans V (at D i j) total (at 'values i hi wi j hj zj)
                (s/sym total (at D i j)
                  (s/trans total (lp/objective Z (at D i) n) (at D i j) (at readi I) (at readj (at D i))))))))))))
(def theorem-specs [forward-spec backward-spec])
(def deps '[rainbow.math.sums.one-hot-value])
(defn install [env] (support/extend-with env :expr-sum-one-hot-pair theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.one-hot-pair))
