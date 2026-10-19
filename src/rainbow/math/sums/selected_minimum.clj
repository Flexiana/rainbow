(ns rainbow.math.sums.selected-minimum
  "A one-hot selected minimum among non-excluded entries. The exclusion penalty
  can have either sign; the dominance premise is used only where exclusion is zero."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.logic.proposition :as prop]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le eqv refl sym]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.one-hot-selects :as selects]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))
(def bits-spec
  (let [complement (a/sub b/one 'x) product (mul 'x complement)
        comp-nn (s/le-transport (a/sub 'x 'x) s/zero complement complement
                  (a/ring-eq (a/sub 'x 'x) s/zero) (refl complement)
                  (call 'signed/add-right-monotone 'x b/one (a/neg 'x) 'upper))
        prod-nn (s/le-transport (mul 'x s/zero) s/zero product product
                  (call 'signed/multiply-zero-right 'x) (refl product)
                  (call 'signed/multiply-left-monotone 'x s/zero complement 'nonnegative comp-nn))]
    (s/spec 'signed/unit-bounds-polynomial-is-binary
      [['x signed] ['nonnegative (le s/zero 'x)] ['upper (le 'x b/one)] ['polynomial (le product s/zero)]]
      (prop/disjunction (eqv 'x s/zero) (eqv 'x b/one))
      (call 'signed/zero-one-of-boolean-polynomial 'x
        (call 'signed/at-most-antisymmetric product s/zero 'polynomial prod-nn)))))
(defn binary [W n] (s/all-below n #(prop/disjunction (eqv (at W %) s/zero) (eqv (at W %) b/one))))
(defn witness-parts [W B d value n i]
  [(s/below i n) (eqv (at W i) b/one) (eqv (at B i) s/zero) (eqv value (at d i))])
(defn minimum [W B d value n]
  [(prop/existence [:succ [:zero]] nat
     (f/lam [['entry nat]] (b/conjunction (witness-parts W B d value n 'entry))))
   (f/forall [['entry nat] ['below (s/below 'entry n)] ['available (eqv (at B 'entry) s/zero)]]
     (le value (at d 'entry)))])
(def minimum-spec
  (let [W 'weights B 'excluded d 'values value 'value n 'n
        weighted (lp/objective W d n)
        global (f/lam [['entry nat] ['below (s/below 'entry n)] ['available (eqv (at B 'entry) s/zero)]]
                 (let [di (at d 'entry) bi (at B 'entry)]
                   (s/le-transport value value (add di (mul 'penalty bi)) di (refl value)
                     (a/chain (add di (mul 'penalty bi))
                       [(add di (mul 'penalty s/zero))
                        (s/add-cong di di (mul 'penalty bi) (mul 'penalty s/zero) (refl di)
                          (a/mul-cong 'penalty 'penalty bi s/zero (refl 'penalty) 'available))]
                       [(add di s/zero) (s/add-cong di di (mul 'penalty s/zero) s/zero (refl di)
                                         (call 'signed/multiply-zero-right 'penalty))]
                       [di (call 'signed/add-zero-right di)])
                     (at 'dominates 'entry 'below))))
        goal (first (minimum W B d value n))
        selected-type (fn [i]
                        [(s/below i n) (eqv (at W i) b/one)
                         (f/forall [['X family]] (eqv (lp/objective W 'X n) (at 'X i)))])
        found (at (call 'signed/one-hot-selects W n 'nonnegative 'binary 'unit-sum) goal
                (f/lam [['index nat] ['selected (b/conjunction (selected-type 'index))]]
                  (let [pieces (selected-type 'index) hi (b/extract pieces 0 'selected)
                        hw (b/extract pieces 1 'selected) reads (b/extract pieces 2 'selected)
                        wi (at W 'index) bi (at B 'index)
                        bound (s/le-transport (add wi bi) (add b/one bi) b/one b/one
                                (s/add-cong wi b/one bi bi hw (refl bi)) (refl b/one) (at 'disjoint 'index hi))
                        nonpos (s/le-transport (add (add b/one bi) (a/neg b/one)) bi
                                 (a/sub b/one b/one) s/zero
                                 (a/ring-eq (add (add b/one bi) (a/neg b/one)) bi)
                                 (a/ring-eq (a/sub b/one b/one) s/zero)
                                 (call 'signed/add-right-monotone (add b/one bi) b/one (a/neg b/one) bound))
                        zero (call 'signed/at-most-antisymmetric bi s/zero nonpos (at 'excluded-nonnegative 'index hi))
                        value-eq (s/trans value weighted (at d 'index) 'weighted-value (at reads d))]
                    (f/app (f/const* 'proposition/witness [[:succ [:zero]]]) nat
                      (f/lam [['entry nat]] (b/conjunction (witness-parts W B d value n 'entry))) 'index
                      (b/conjoin (witness-parts W B d value n 'index) [hi hw zero value-eq])))))]
    (s/spec 'signed/one-hot-excluded-minimum
      [['weights family] ['excluded family] ['values family] ['value signed] ['penalty signed] ['n nat]
       ['nonnegative (lp/nonnegative W n)] ['binary (binary W n)] ['unit-sum (eqv (sum W n) b/one)]
       ['weighted-value (eqv value weighted)] ['excluded-nonnegative (lp/nonnegative B n)]
       ['disjoint (s/all-below n #(le (add (at W %) (at B %)) b/one))]
       ['dominates (s/all-below n #(le value (add (at d %) (mul 'penalty (at B %)))))]]
      (b/conjunction (minimum W B d value n))
      (b/conjoin (minimum W B d value n) [found global]))))
(def theorem-specs [bits-spec minimum-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.one-hot-selects])
(defn install [env] (support/extend-with env :expr-sum-selected-minimum theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.selected-minimum))
