(ns rainbow.math.sums.permutation-invariant
  "Nonlinear two-coordinate sums are invariant under a binary permutation matrix.
  Selection is derived from one-hot columns, not supplied as an external decoder."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.assign-dual :as assignment]
            [rainbow.math.rational.signed.one-hot-selects :as select]))
(def matrix (f/arrow nat family))
(def operation (f/arrow signed (f/arrow signed signed)))
(defn respects [G]
  (f/forall [['pi-a signed] ['pi-b signed] ['pi-c signed] ['pi-d signed]
             ['pi-ac (eqv 'pi-a 'pi-c)] ['pi-bd (eqv 'pi-b 'pi-d)]]
    (eqv (at G 'pi-a 'pi-b) (at G 'pi-c 'pi-d))))
(defn weighted [S P] (f/lam [['pi-job nat]] (mul (at S 'pi-job) (at P 'pi-job))))
(defn column [X k] (f/lam [['pi-job nat]] (at X 'pi-job k)))
(defn selected-value [X P n k] (sum (weighted (column X k) P) n))
(defn transformed [X P n] (f/lam [['pi-position nat]] (selected-value X P n 'pi-position)))
(defn binary [S n] (s/all-below n #(a/disj (eqv (at S %) s/zero) (eqv (at S %) a/one))))
(defn nonnegative [S n] (s/all-below n #(le s/zero (at S %))))
(defn binary-cells [X n]
  (f/forall [['pi-row nat] ['pi-rb (s/below 'pi-row n)] ['pi-col nat] ['pi-cb (s/below 'pi-col n)]]
    (a/disj (eqv (at X 'pi-row 'pi-col) s/zero) (eqv (at X 'pi-row 'pi-col) a/one))))
(defn- both [x y] (call 'proposition/conjunction x y))
(defn- right [x y h] (call 'proposition/right x y h))
(defn- reads [S n job]
  (f/forall [['pi-function family]] (eqv (sum (weighted S 'pi-function) n) (at 'pi-function job))))
(defn- selection [S n job]
  (both (s/below job n) (both (eqv (at S job) a/one) (reads S n job))))
(def one-hot-operation-spec
  (let [S 'pi-selector P 'pi-first W 'pi-second G 'pi-operation n 'pi-size
        GPW (f/lam [['pi-job nat]] (at G (at P 'pi-job) (at W 'pi-job)))
        lhs (at G (sum (weighted S P) n) (sum (weighted S W) n))
        rhs (sum (weighted S GPW) n) goal (eqv lhs rhs)
        evidence (call 'signed/one-hot-selects S n 'pi-nonnegative 'pi-binary 'pi-unit)]
    (s/spec 'signed/one-hot-preserves-binary-operation
      [[S family] [P family] [W family] [G operation] [n nat]
       ['pi-respects (respects G)] ['pi-nonnegative (nonnegative S n)]
       ['pi-binary (binary S n)] ['pi-unit (eqv (sum S n) a/one)]]
      goal
      (at evidence goal
        (f/lam [['pi-picked nat] ['pi-evidence (selection S n 'pi-picked)]]
          (let [r (right (eqv (at S 'pi-picked) a/one) (reads S n 'pi-picked)
                    (right (s/below 'pi-picked n)
                      (both (eqv (at S 'pi-picked) a/one) (reads S n 'pi-picked)) 'pi-evidence))
                picked (at G (at P 'pi-picked) (at W 'pi-picked))]
            (s/trans lhs picked rhs
              (at 'pi-respects (sum (weighted S P) n) (sum (weighted S W) n)
                (at P 'pi-picked) (at W 'pi-picked) (at r P) (at r W))
              (sym rhs picked (at r GPW)))))))))
(def weighted-conservation-spec
  (let [X 'pi-matrix V 'pi-values n 'pi-size
        B (f/lam [['pi-i nat] ['pi-k nat]] (mul (at X 'pi-i 'pi-k) (at V 'pi-i)))
        A (f/lam [['pi-i nat] ['pi-k nat]] (mul (at V 'pi-i) (at X 'pi-i 'pi-k)))
        lhs (sum (f/lam [['pi-k nat]] (selected-value X V n 'pi-k)) n)
        rhs (sum (f/lam [['pi-i nat]] (at V 'pi-i)) n)]
    (s/spec 'signed/permutation-row-weight-conservation
      [[X matrix] [V family] [n nat] ['pi-rows (assignment/row-sums-one X n)]]
      (eqv lhs rhs)
      (a/chain lhs
        [(a/double-sum B n) (sym (a/double-sum B n) lhs (call 'signed/expr-sum-value-swap B n n))]
        [(a/double-sum A n)
         (a/sum-cong (f/lam [['pi-i nat]] (sum (a/matrix-row B 'pi-i) n))
                     (f/lam [['pi-i nat]] (sum (a/matrix-row A 'pi-i) n)) n 'pi-outer
           (fn [i _] (a/sum-cong (a/matrix-row B i) (a/matrix-row A i) n 'pi-inner
             (fn [k _] (call 'signed/multiply-commutative (at X i k) (at V i))))))]
        [rhs (call 'signed/double-sum-row-weights V X n 'pi-rows)]))))
(def invariant-spec
  (let [X 'pi-matrix P 'pi-first W 'pi-second G 'pi-operation n 'pi-size
        values (f/lam [['pi-job nat]] (at G (at P 'pi-job) (at W 'pi-job)))
        source (f/lam [['pi-k nat]] (at G (selected-value X P n 'pi-k) (selected-value X W n 'pi-k)))
        target (f/lam [['pi-k nat]] (selected-value X values n 'pi-k))]
    (s/spec 'signed/permutation-binary-operation-sum-invariant
      [[X matrix] [P family] [W family] [G operation] [n nat]
       ['pi-respects (respects G)] ['pi-nonnegative (assignment/nonnegative-cells X n)]
       ['pi-binary (binary-cells X n)] ['pi-rows (assignment/row-sums-one X n)]
       ['pi-cols (assignment/col-sums-one X n)]]
      (eqv (sum source n) (sum values n))
      (s/trans (sum source n) (sum target n) (sum values n)
        (a/sum-cong source target n 'pi-at
          (fn [k hk]
            (call 'signed/one-hot-preserves-binary-operation (column X k) P W G n 'pi-respects
              (f/lam [['pi-selected nat] ['pi-bound (s/below 'pi-selected n)]]
                (at 'pi-nonnegative 'pi-selected 'pi-bound k hk))
              (f/lam [['pi-selected nat] ['pi-bound (s/below 'pi-selected n)]]
                (at 'pi-binary 'pi-selected 'pi-bound k hk))
              (at 'pi-cols k hk))))
        (call 'signed/permutation-row-weight-conservation X values n 'pi-rows)))))
(def theorem-specs [one-hot-operation-spec weighted-conservation-spec invariant-spec])
(defn extend-environment [env]
  (reduce (fn [checked spec]
            (println :permutation-invariant :installing (:name spec)) (flush)
            (support/add-spec-shared checked :expr-sum-permutation-invariant spec))
          (-> env assignment/extend-environment select/extend-environment) theorem-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
