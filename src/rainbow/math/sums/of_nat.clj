(ns rainbow.math.sums.of-nat
  "The bridge between a natural-number count written as the signed literal of-nat n = n/1 (the form
  the checkers use, e.g. A m = sum p) and a sum of n equal terms:
    nnrat/of-nat-successor        : (k + 1)/1 ~ k/1 + 1                  (nnrat equivalence)
    signed/of-nat-successor       : of-nat (k + 1) ~ of-nat k + 1
    signed/expr-sum-constant-of-nat : sum_{i<n} c ~ c * of-nat n
  The nnrat step unfolds to succ (k 1) = (k 1 + 1) 1 in nat, closed by multiply-one-right,
  add-successor-right and nat-add-zero-right (k 1 does not reduce: multiplication recurses on the left)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed call at sum mul eqv refl sym trans]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.nat.semiring :as nat-semiring]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.geometric-bridge :as geometric]
            [rainbow.math.linear.matrix.affine-general-rate-certificate :as rate]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]))

(def type-level [:succ [:zero]])
(def prop-level [:zero])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def one (f/const* 'signed/one []))
(def nn-one (f/const* 'nnrat/one []))
(defn- add [x y] (call 'signed/add x y))
(defn- nadd [x y] (call 'algebra/nat-add x y))
(defn- nmul [x y] (call 'nat/multiply x y))
(def nat-one (s/succ s/nz))
(defn make [n] (call 'nnrat/make n s/nz))
(defn of-nat [n] (call 'signed/from-nnrat (make n)))
(defn- eqn [x y] (f/equality type-level nat x y))
(defn- nsym [x y h] (f/app (f/const* 'equality/symmetric [type-level]) nat x y h))
(defn- ntrans [x y z h k] (f/app (f/const* 'equality/transitive [type-level]) nat x y z h k))
(defn- ncongr [ff x y h] (f/app (f/const* 'equality/congruent-function [type-level type-level]) nat nat ff x y h))
(defn- times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (call 'signed/multiply-one-left x)]))

;; (k + 1)/1 ~ k/1 + 1/1: unfolds to  succ (k 1) = (k 1 + 1) 1
(def nnrat-successor-spec
  (let [X (nmul 'k nat-one)
        e1 (call 'nat/multiply-one-right (nadd X nat-one))                 ; (X + 1) 1 = X + 1
        e2 (call 'nat/add-successor-right X s/nz)                          ; X + succ 0 = succ (X + 0)
        e3 (call 'algebra/nat-add-zero-right X)                            ; X + 0 = X
        succ-fn (f/lam [['sk nat]] (s/succ 'sk))
        step (ncongr succ-fn X (nadd X s/nz) (nsym (nadd X s/nz) X e3))    ; succ X = succ (X + 0)
        proof (ntrans (s/succ X) (s/succ (nadd X s/nz)) (nmul (nadd X nat-one) nat-one) step
                      (ntrans (s/succ (nadd X s/nz)) (nadd X nat-one) (nmul (nadd X nat-one) nat-one)
                              (nsym (nadd X nat-one) (s/succ (nadd X s/nz)) e2)
                              (nsym (nmul (nadd X nat-one) nat-one) (nadd X nat-one) e1)))]
    {:name 'nnrat/of-nat-successor :universes []
     :type (f/forall [['k nat]] (call 'nnrat/equivalent (make (s/succ 'k)) (call 'nnrat/add (make 'k) nn-one)))
     :value (f/lam [['k nat]] proof)}))

;; of-nat (k + 1) ~ of-nat k + 1
(def signed-successor-spec
  (let [L (make (s/succ 'k)) R (call 'nnrat/add (make 'k) nn-one)]
    (s/spec 'signed/of-nat-successor [['k nat]]
            (eqv (of-nat (s/succ 'k)) (add (of-nat 'k) one))
            (trans (of-nat (s/succ 'k)) (call 'signed/from-nnrat R) (add (of-nat 'k) one)
                   (call 'signed/from-nnrat-respects-equivalence L R (call 'nnrat/of-nat-successor 'k))
                   (sym (add (of-nat 'k) one) (call 'signed/from-nnrat R) (call 'signed/from-nnrat-add (make 'k) nn-one))))))

;; sum_{i<n} c ~ c * of-nat n
(def sum-constant-spec
  (let [C (f/lam [['ci nat]] 'c)
        claim (fn [k] (eqv (sum C k) (mul 'c (of-nat k))))]
    (s/spec 'signed/expr-sum-constant-of-nat [['c signed] ['n nat]]
            (claim 'n)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['sc-k nat]] (claim 'sc-k))
                   (sym (mul 'c (of-nat s/nz)) s/zero (call 'signed/multiply-zero-right 'c))
                   (f/lam [['sc-j nat] ['sc-ih (claim 'sc-j)]]
                          (let [j 'sc-j m (mul 'c (of-nat j))]
                            (a/chain (add (sum C j) 'c)
                                     [(add m 'c) (s/add-cong (sum C j) m 'c 'c 'sc-ih (refl 'c))]
                                     [(add m (mul 'c one)) (s/add-cong m m 'c (mul 'c one) (refl m) (sym (mul 'c one) 'c (times-one 'c)))]
                                     [(mul 'c (add (of-nat j) one)) (sym (mul 'c (add (of-nat j) one)) (add m (mul 'c one))
                                                                         (call 'signed/multiply-distributes-add-left 'c (of-nat j) one))]
                                     [(mul 'c (of-nat (s/succ j))) (a/mul-cong 'c 'c (add (of-nat j) one) (of-nat (s/succ j)) (refl 'c)
                                                                               (sym (of-nat (s/succ j)) (add (of-nat j) one) (call 'signed/of-nat-successor j)))])))
                   'n))))

(def theorem-specs [nnrat-successor-spec signed-successor-spec sum-constant-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.flow-cut rainbow.math.nat.semiring rainbow.math.nat.strict-below-more rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.rational.signed.multiply-ring rainbow.math.linear.matrix.action-scale])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-of-nat theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.of-nat))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
