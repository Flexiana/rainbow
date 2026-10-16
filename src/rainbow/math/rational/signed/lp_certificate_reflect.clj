(ns rainbow.math.rational.signed.lp-certificate-reflect
  "LP optimality certificates by reflection over finite row and column lists.

  The Boolean checker decides primal feasibility, dual feasibility, both
  nonnegativity conditions and the signed-equivalence objective gap. Its native,
  axiom-free soundness theorem applies the existing list-quantified LP theorem.
  A concrete certificate needs one theorem application and a true-reflexivity
  witness; the kernel computes the checker on the supplied data. The application
  still contains that data, so total proof size is not independent of the input."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def type-level [:succ [:zero]])
(defn- c [alias] (f/const* alias []))
(defn- app [g & xs] (apply f/app g xs))
(def signed (c 'signed/SignedRational))
(def bool (c 'data/Bool))
(def true-value (c 'data/true))
(defn- list-of [A] (app (f/const* 'data/List [data-level]) A))
(defn- nil-of [A] (app (f/const* 'data/nil [data-level]) A))
(defn- cons-of [A x xs] (app (f/const* 'data/cons [data-level]) A x xs))
(defn- eq-true [b] (f/equality type-level bool b true-value))
(defn- both [a b] (app (c 'boolean/and) a b))
(defn- left [a b h] (app (c 'boolean/and-implies-left) a b h))
(defn- right [a b h] (app (c 'boolean/and-implies-right) a b h))
(defn- decide [a b] (app (c 'signed/decide-at-most) a b))
(defn- smul [a b] (app (c 'signed/multiply) a b))
(defn- sle [a b] (app (c 'signed/at-most) a b))
(defn- sum [A g xs] (app (f/const* 'signed/map-sum [U]) A g xs))
(defn- all-at-most [A g h xs]
  (app (f/const* 'signed/all-at-most [U]) A g h xs))
(defn- all-decide [A g h xs]
  (app (f/const* 'lp/all-at-most-decide [U]) A g h xs))
(defn- all-sound [A g h xs proof]
  (app (f/const* 'lp/all-at-most-decide-sound [U]) A g h xs proof))

(def ^:private all-bindings
  [['A type-u] ['f (f/arrow 'A signed)] ['g (f/arrow 'A signed)]])

(def all-at-most-decide-spec
  {:name 'lp/all-at-most-decide :kind :definition :universes ['u]
   :transparency :reducible
   :type (f/forall all-bindings (f/arrow (list-of 'A) bool))
   :value
   (f/lam (conj all-bindings ['xs (list-of 'A)])
     (app (f/const* 'data/List.rec [data-level type-level]) 'A
          (f/lam [['ignored (list-of 'A)]] bool)
          true-value
          (f/lam [['head 'A] ['tail (list-of 'A)] ['ih bool]]
            (both (decide (app 'f 'head) (app 'g 'head)) 'ih))
          'xs))})

(defn- all-sound-at [xs]
  (f/arrow (eq-true (all-decide 'A 'f 'g xs))
           (all-at-most 'A 'f 'g xs)))

(def all-at-most-decide-sound-spec
  {:name 'lp/all-at-most-decide-sound :universes ['u]
   :type (f/forall (conj all-bindings ['xs (list-of 'A)]) (all-sound-at 'xs))
   :value
   (f/lam (conj all-bindings ['xs (list-of 'A)])
     (app (f/const* 'data/List.rec [data-level [:zero]]) 'A
          (f/lam [['ys (list-of 'A)]] (all-sound-at 'ys))
          (f/lam [['h (eq-true (all-decide 'A 'f 'g (nil-of 'A)))]]
            (c 'proposition/trivial))
          (f/lam [['head 'A] ['tail (list-of 'A)] ['ih (all-sound-at 'tail)]
                  ['h (eq-true (all-decide 'A 'f 'g (cons-of 'A 'head 'tail)))]]
            (let [here (decide (app 'f 'head) (app 'g 'head))
                  rest (all-decide 'A 'f 'g 'tail)]
              (app (f/const* 'signed/all-at-most-cons [U]) 'A 'f 'g 'head 'tail
                   (app (c 'signed/decide-at-most-true-sound)
                        (app 'f 'head) (app 'g 'head) (left here rest 'h))
                   (app 'ih (right here rest 'h)))))
          'xs))})

(def ^:private certificate-bindings
  [['A type-u] ['B type-u] ['M (f/arrow 'A (f/arrow 'B signed))]
   ['b (f/arrow 'A signed)] ['c (f/arrow 'B signed)]
   ['x (f/arrow 'B signed)] ['y (f/arrow 'A signed)]
   ['rows (list-of 'A)] ['cols (list-of 'B)]])
(def ^:private certificate-arguments ['A 'B 'M 'b 'c 'x 'y 'rows 'cols])
(defn- activity [plan]
  (f/lam [['i 'A]]
    (sum 'B (f/lam [['j 'B]] (smul (app (app 'M 'i) 'j) (app plan 'j))) 'cols)))
(def ^:private dual-price
  (f/lam [['j 'B]]
    (sum 'A (f/lam [['i 'A]] (smul (app (app 'M 'i) 'j) (app 'y 'i))) 'rows)))
(defn- zero-on [A] (f/lam [['ignored A]] (c 'signed/zero)))
(defn- objective [plan]
  (sum 'B (f/lam [['j 'B]] (smul (app 'c 'j) (app plan 'j))) 'cols))
(def ^:private dual-objective
  (sum 'A (f/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i))) 'rows))
(def ^:private clauses
  [(all-decide 'A (activity 'x) 'b 'rows)
   (all-decide 'B 'c dual-price 'cols)
   (all-decide 'B (zero-on 'B) 'x 'cols)
   (all-decide 'A (zero-on 'A) 'y 'rows)
   (app (c 'signed/decide-equivalent) dual-objective (objective 'x))])
(defn- conjunction [clauses]
  (reduce (fn [tail head] (both head tail)) (last clauses) (reverse (butlast clauses))))
(def ^:private checker
  (apply app (f/const* 'lp/certificate-check [U]) certificate-arguments))

(def certificate-check-spec
  {:name 'lp/certificate-check :kind :definition :universes ['u]
   :transparency :reducible
   :type (f/forall certificate-bindings bool)
   :value (f/lam certificate-bindings (conjunction clauses))})

(def ^:private conclusion
  (f/forall [['candidate (f/arrow 'B signed)]
             ['candidate-feasible (all-at-most 'A (activity 'candidate) 'b 'rows)]
             ['candidate-nonnegative (all-at-most 'B (zero-on 'B) 'candidate 'cols)]]
    (sle (objective 'candidate) (objective 'x))))

(defn- clause-proofs [clauses proof]
  (if (= 1 (count clauses)) [proof]
    (let [a (first clauses) b (conjunction (rest clauses))]
      (into [(left a b proof)] (clause-proofs (rest clauses) (right a b proof))))))

(def certificate-check-sound-spec
  {:name 'lp/certificate-check-sound :universes ['u]
   :type (f/forall (conj certificate-bindings ['checked (eq-true checker)]) conclusion)
   :value
   (f/lam (conj certificate-bindings ['checked (eq-true checker)])
     (let [[primal dual x-positive y-positive gap] (clause-proofs clauses 'checked)]
       (apply app (f/const* 'optimization/signed-lp-optimality-certificate-on [U])
              (into certificate-arguments
                    [(all-sound 'A (activity 'x) 'b 'rows primal)
                     (all-sound 'B 'c dual-price 'cols dual)
                     (all-sound 'B (zero-on 'B) 'x 'cols x-positive)
                     (all-sound 'A (zero-on 'A) 'y 'rows y-positive)
                     (app (c 'signed/decide-equivalent-true-sound)
                          dual-objective (objective 'x) gap)]))))})

(def definition-specs [all-at-most-decide-spec certificate-check-spec])
(def theorem-specs [all-at-most-decide-sound-spec certificate-check-sound-spec])
(def deps
  '[rainbow.math.rational.signed.lp-duality-on rainbow.math.rational.signed.decide-equivalence])
(defn install [checked-environment]
  (support/extend-with checked-environment :signed-lp-certificate-reflect
    [all-at-most-decide-spec all-at-most-decide-sound-spec
     certificate-check-spec certificate-check-sound-spec]))
(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-certificate-reflect))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
