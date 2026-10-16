(ns rainbow.math.nat.ring-reflect-test
  "The reflection definitions compute what they should: equal polynomials normalize
  to the same Horner form, unequal ones do not, and normalizing never changes the
  value. Everything here is computed by the kernel's own normalizer."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring-reflect :as reflect]))

(def ^:private env
  (delay (reflect/extend-environment
          (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")))))

(defn- core [surface]
  (let [r (elaborate/core-expression @env surface)]
    (assert (= :elaborated (:status r)) (pr-str r))
    (:term r)))
(defn- normal [surface]
  (let [r (kernel/normalize @env (core surface))]
    (assert (= :normalized (:status r)) (pr-str r))
    (:term r)))
(defn- c [alias] (function/const* alias []))
(defn- num [n] (nth (iterate #(function/app (c 'data/succ) %) (c 'data/zero)) n))

(defn- x [i] (function/app (c 'ring/atom) (num i)))
(defn- k [n] (function/app (c 'ring/const) (num n)))
(defn- e+ [& xs] (reduce #(function/app (c 'ring/add) %1 %2) xs))
(defn- e* [& xs] (reduce #(function/app (c 'ring/mul) %1 %2) xs))

(defn- decides [l r] (normal (reflect/pol-equal (reflect/normalize l) (reflect/normalize r))))
(def ^:private yes (delay (normal (c 'data/true))))
(def ^:private no (delay (normal (c 'data/false))))

(deftest definitions-are-accepted
  (is (= 10 (count (reflect/definition-ids @env))))
  (doseq [[alias id] (reflect/definition-ids @env)]
    (is id (str alias))
    (is (= #{} (kernel/axioms @env id)) (str alias))))

(deftest identities-normalize-to-the-same-form
  (let [a (x 0) b (x 1) c3 (x 2)
        s3 (e+ a b c3)
        cube-expanded (apply e+ (for [p [a b c3] q [a b c3] r [a b c3]] (e* p q r)))]
    (doseq [[what l r]
            [["commutativity" (e+ a b) (e+ b a)]
             ["associativity" (e* (e* a b) c3) (e* a (e* b c3))]
             ["distributivity" (e* a (e+ b c3)) (e+ (e* a b) (e* a c3))]
             ["variable order reversed" (e* c3 b a) (e* a b c3)]
             ["zero is eliminated" (e+ (e* (k 0) a) b) b]
             ["constants fold" (e+ (k 2) (k 3) a) (e+ a (k 5))]
             ["(a+b)^2" (e* (e+ a b) (e+ a b)) (e+ (e* a a) (e* (k 2) a b) (e* b b))]
             ["(a+b+c)^3, 27 monomials" (e* s3 s3 s3) cube-expanded]]]
      (testing what (is (= @yes (decides l r)))))))

(deftest non-identities-do-not
  (let [a (x 0) b (x 1)]
    (doseq [[what l r] [["a+b vs a" (e+ a b) a]
                        ["(a+b)^2 vs a^2+b^2" (e* (e+ a b) (e+ a b)) (e+ (e* a a) (e* b b))]
                        ["2a vs a" (e* (k 2) a) a]
                        ["a*b vs a+b" (e* a b) (e+ a b)]]]
      (testing what (is (= @no (decides l r)))))))

(deftest addition-keeps-canonical-zero-and-nonzero-coefficients
  ;; Removing the addition branch's zero inspection must keep normalization
  ;; complete for expressions containing zero products, repeated indices, and
  ;; coefficients which are themselves multivariate polynomials.
  (let [a (x 0) b (x 1) c3 (x 2) z (k 0)]
    (doseq [[lhs rhs]
            [[(e+ (e* z a) (e* z a)) z]
             [(e+ (e* z a) a (e* a z)) a]
             [(e+ (e* a a) (e* a a)) (e* (k 2) a a)]
             [(e+ (e* (e+ a b) a) (e* (e+ c3 z) a))
              (e* (e+ a b c3) a)]
             [(e* (e+ (e* z a) (e* b z)) (e+ a b c3)) z]]]
      (is (= (normal (reflect/normalize lhs)) (normal (reflect/normalize rhs)))))))

(deftest normalizing-keeps-the-value
  ;; atoms 0, 1, 2 take the values 3, 5, 7
  (let [values (function/lam [['i (c 'data/Nat)]]
                             (function/app (c 'algebra/nat-add) 'i
                                           (function/app (c 'algebra/nat-add) 'i (num 3))))
        a (x 0) b (x 1) c3 (x 2)]
    (doseq [e [(e* (e+ a b) (e+ b c3)) (e* (e+ a (k 2)) (e+ a (k 2)) c3) (e+ (e* (k 0) a) (e* b b))]]
      (is (= (normal (reflect/denote values e))
             (normal (reflect/eval-pol values (reflect/normalize e))))))))

(deftest reification-denotes-the-goal-itself
  ;; denote env (reify t) is definitionally t, over the goal's free variables
  (let [nat (c 'data/Nat)
        m #(function/app (c 'nat/multiply) %1 %2) p #(function/app (c 'algebra/nat-add) %1 %2)]
    (doseq [t [(p 'a 'b) (m (p 'a (num 2)) (p 'b 'a)) (m (m 'c 'b) (p 'a [:nat 7]))]]
      (let [[e atoms] (reflect/reify t)
            statement (function/forall [['a nat] ['b nat] ['c nat]]
                                       (function/equality [:succ [:zero]] nat
                                                          (reflect/denote (reflect/atom-table atoms) e) t))
            proof (function/lam [['a nat] ['b nat] ['c nat]]
                                (function/app (function/const* 'equality/reflexive [[:succ [:zero]]]) nat t))
            r (kernel/check @env (core proof) (core statement))]
        (is (= :checked (:status r)) (pr-str t))))))

(deftest atom-table-does-not-capture-user-symbols
  (doseq [name '[ring-table-index ring-table-ignored ring-table-predecessor
                ring-table-result ring-reflect-polynomial ring-table-index-0
                ring-table-index-1 ring-table-predecessor-0 ring-table-result-0]
          atoms [[name] ['other name] [name 'other]
                 [(function/app 'f name) 'other name]]]
    (let [bindings [[name reflect/nat] ['other reflect/nat]
                    ['f (function/arrow reflect/nat reflect/nat)]]
          table (reflect/atom-table atoms)]
      (doseq [i (range (+ 2 (count atoms)))]
        (testing (str name " in " atoms " at " i)
          (let [value (nth atoms (min i (dec (count atoms))))
                statement (function/forall bindings
                            (function/equality [:succ [:zero]] reflect/nat
                              (function/app table [:nat i]) value))
                proof (function/lam bindings
                        (function/app (function/const* 'equality/reflexive [[:succ [:zero]]])
                                      reflect/nat value))]
            (is (= :checked (:status (kernel/check @env (core proof) (core statement)))))))))))

(deftest reification-preserves-arbitrary-natural-values
  (doseq [n [0 7 Long/MAX_VALUE (bigint Long/MAX_VALUE) 100000000000000000000N]
          successors [0 1 2]]
    (let [t (nth (iterate #(function/app (c 'data/succ) %) [:nat n]) successors)]
      (testing (str n " with " successors " successors")
        (is (= [(function/app (c 'ring/const) [:nat (+' n successors)]) []]
               (reflect/reify t)))))))

(deftest reification-does-not-erase-malformed-input
  ;; Unknown terms stay atoms so elaboration/type checking can reject them.
  ;; Reification must not silently repair invalid literal or constant syntax.
  (doseq [t (concat
             [[:nat] [:nat -1] [:nat 1/2] [:nat 1.0] [:nat 1M] [:nat nil]
              [:nat 1 :extra] (function/app (c 'data/succ) [:nat -1])]
             (for [alias ['algebra/nat-add 'nat/multiply]
                   head [[:const alias] [:const alias [] :extra]
                         [:const alias [[:zero]]]]]
               (function/app head [:nat 1] [:nat 2])))]
    (testing (pr-str t)
      (is (= [(function/app (c 'ring/atom) [:nat 0]) [t]]
             (reflect/reify t))))))
