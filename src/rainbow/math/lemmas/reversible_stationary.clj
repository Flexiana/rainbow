(ns rainbow.math.lemmas.reversible-stationary
  "General lemmas: reversible stationary. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(def invariant-spec
  (let [flow (sum (f/lam [['fi nat]] (mul (at 'pot 'fi) (at 'P 'fi 'j))) 'n)
        back (sum (f/lam [['bi nat]] (mul (at 'pot 'j) (at 'P 'j 'bi))) 'n)
        row (f/lam [['ri nat]] (at 'P 'j 'ri))]
    (s/spec 'signed/detailed-balance-invariant
            [['P matrix] ['pot family] ['n nat]
             ['hrow (s/all-below 'n #(eqv (sum (f/lam [['rc nat]] (at 'P % 'rc)) 'n) one))]
             ['hbal (f/forall [['bu nat] ['bu-bound (below 'bu 'n)] ['bv nat] ['bv-bound (below 'bv 'n)]]
                              (eqv (mul (at 'pot 'bu) (at 'P 'bu 'bv)) (mul (at 'pot 'bv) (at 'P 'bv 'bu))))]
             ['j nat] ['hj (below 'j 'n)]]
            (eqv flow (at 'pot 'j))
            (a/chain flow
                     [back (a/sum-cong (f/lam [['fi nat]] (mul (at 'pot 'fi) (at 'P 'fi 'j)))
                                       (f/lam [['bi nat]] (mul (at 'pot 'j) (at 'P 'j 'bi))) 'n 'ci
                                       (fn [i hi] (at 'hbal i hi 'j 'hj)))]
                     [(mul (at 'pot 'j) (sum row 'n))
                      (sym (mul (at 'pot 'j) (sum row 'n)) back (call 'signed/expr-sum-value-scale-left row (at 'pot 'j) 'n))]
                     [(mul (at 'pot 'j) one)
                      (a/mul-cong (at 'pot 'j) (at 'pot 'j) (sum row 'n) one (refl (at 'pot 'j)) (at 'hrow 'j 'hj))]
                     [(mul one (at 'pot 'j)) (call 'signed/multiply-commutative (at 'pot 'j) one)]
                     [(at 'pot 'j) (call 'signed/multiply-one-left (at 'pot 'j))]))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(defn conjoin [ps proofs]
  (if (= 1 (count ps)) (first proofs)
      (call 'proposition/conjoin (first ps) (conjunction (rest ps)) (first proofs) (conjoin (rest ps) (rest proofs)))))

(def accepted-bridge-spec
  (s/spec 'signed/reversible-accepted-stationary
          [['env family] ['n nat] ['accepted (f/equality type-level signed (call 'signed/reversible 'env 'n) one)]]
          (f/equality type-level signed (call 'signed/stationary 'env 'n) one)
          (call 'signed/stationary-complete 'env 'n
                (call 'signed/reversible-conditions-stationary 'env 'n (call 'signed/reversible-sound 'env 'n 'accepted)))))

(def theorem-specs [invariant-spec accepted-bridge-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      s/extend-environment
      a/extend-environment
      units/extend-environment
      divmod/extend-environment
      pairs/extend-environment
      (support/extend-with :expr-sum-reversible-stationary theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
