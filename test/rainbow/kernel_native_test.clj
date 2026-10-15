(ns rainbow.kernel-native-test
  "Natural-number literals and the kernel's native nat operations.

  The kernel computes six reducible nat definitions natively on literals. Each is
  pinned to the content id of the exact definition it replaces; these tests check
  that every pin is still that definition, and that every native result equals the
  definition's own unary reduction (its value applied to unary numerals, which no
  native step can intercept at the top)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as expectation]
            [rainbow.math.linear.matrix.row-length-decider :as row-length]
            [rainbow.math.nat.distance :as distance]
            [rainbow.math.nat.linear-order :as linear-order]))

(def ^:private env
  (delay
    (let [loaded (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (assert (= :replayed (:status loaded)))
      (-> (:environment loaded)
          linear-order/extend-environment
          distance/extend-environment
          expectation/extend-environment
          row-length/extend-environment))))

(def ^:private pinned
  "alias -> the arity the kernel table records"
  '{algebra/nat-add 2 nat/multiply 2 nat/predecessor 1 nat/distance 2
    nat/decide-equality 2 nat/decide-at-most 2})

(defn- id [alias] (environment/resolve-id @env alias))
(defn- c [alias] [:const (id alias) []])
(defn- unary-numeral [n] (nth (iterate #(vector :app (c 'data/succ) %) (c 'data/zero)) n))
(defn- app [f & args] (reduce #(vector :app %1 %2) f args))
(defn- normal [t]
  (let [r (kernel/normalize @env t)]
    (assert (= :normalized (:status r)) (pr-str r))
    (:term r)))

(deftest every-pin-is-the-current-definition
  (let [table @#'kernel/nat-operations]
    (is (= (set (keys table)) (set (map id (keys pinned)))) "the table names exactly these six definitions")
    (doseq [[alias arity] pinned]
      (testing alias
        (is (= arity (first (get table (id alias)))))
        (is (#{:reducible :semireducible}
             (:rainbow/transparency (environment/declaration @env (id alias)))))))))

(deftest native-operations-agree-with-their-definitions
  (let [inputs (concat (for [a (range 10) b (range 10)] [a b])
                       (let [r (java.util.Random. 20261015)] (repeatedly 40 #(vector (.nextInt r 41) (.nextInt r 41)))))]
    (doseq [[alias arity] pinned
            :let [value (:rainbow/value (environment/declaration @env (id alias)))]
            [a b] inputs
            :let [args (take arity [a b])]]
      (testing (str alias " " (vec args))
        (let [reference (normal (apply app value (map unary-numeral args)))]
          ;; literal arguments, unary arguments, and a mix all give the definition's own result
          (is (= reference (normal (apply app (c alias) (map #(vector :nat %) args)))))
          (is (= reference (normal (apply app (c alias) (map unary-numeral args)))))
          (when (= 2 arity)
            (is (= reference (normal (app (c alias) [:nat a] (unary-numeral b)))))))))))

(deftest literals-denote-unary-numerals
  (testing "a literal has type Nat, and only where Nat exists"
    (is (= (c 'data/Nat) (:type (kernel/infer @env [:nat 7]))))
    (is (= :rejected (:status (kernel/infer (environment/empty-environment) [:nat 7])))))
  (testing "a literal is definitionally its unary numeral, and no other"
    (is (true? (kernel/definitionally-equal? @env [:nat 3] (unary-numeral 3))))
    (is (true? (kernel/definitionally-equal? @env [:nat 0] (c 'data/zero))))
    (is (false? (kernel/definitionally-equal? @env [:nat 3] (unary-numeral 2))))
    (is (false? (kernel/definitionally-equal? @env (app (c 'algebra/nat-add) [:nat 2] [:nat 2]) [:nat 5]))))
  (testing "a recursor computes the same on a literal as on its numeral"
    (let [motive [:lam (c 'data/Nat) (c 'data/Nat) :explicit]
          step [:lam (c 'data/Nat) [:lam (c 'data/Nat) (app (c 'data/succ) (app (c 'data/succ) [:bound 0])) :explicit] :explicit]
          rec #(app [:const (id 'data/Nat.rec) [[:succ [:zero]]]] motive (c 'data/zero) step %)]
      (is (= (normal (rec (unary-numeral 4))) (normal (rec [:nat 4]))))
      (is (= (unary-numeral 8) (normal (rec [:nat 4]))))))
  (testing "public normal forms stay unary"
    (let [result (normal (app (c 'nat/multiply) [:nat 3] [:nat 4]))]
      (is (= (unary-numeral 12) result))
      (is (not-any? #(and (vector? %) (= :nat (first %))) (tree-seq vector? seq result)))))
  (testing "symbolic arguments are unfolded as before, not computed"
    (let [open [:lam (c 'data/Nat) (app (c 'algebra/nat-add) (unary-numeral 2) [:bound 0]) :explicit]]
      (is (= [:lam (c 'data/Nat) (app (c 'data/succ) (app (c 'data/succ) [:bound 0])) :explicit]
             (normal open)))))
  (testing "literal terms are well formed only with natural numbers"
    (is (= :rejected (:status (kernel/infer @env [:nat -1]))))
    (is (= :rejected (:status (kernel/infer @env [:nat 1.5]))))))

(deftest open-arguments-are-reduced-as-before
  ;; native arithmetic only touches closed arguments: on an open term the reduction
  ;; is step for step the one without any native operations
  (let [nat (c 'data/Nat)
        open [:lam nat (app (c 'nat/multiply) (app (c 'algebra/nat-add) [:bound 0] (unary-numeral 3))
                            (app (c 'algebra/nat-add) (unary-numeral 2) [:bound 0])) :explicit]
        with-native (kernel/normalize @env open)
        without (with-redefs-fn {#'kernel/nat-operations {}} #(kernel/normalize @env open))]
    (is (= :normalized (:status with-native)))
    (is (= (:term without) (:term with-native)))
    (is (= (:reductions without) (:reductions with-native)))))

(deftest native-evaluation-never-costs-the-caller-more-than-unfolding
  ;; multiply 0 x unfolds to 0 without looking at x. Evaluating x natively first
  ;; (5,000 recursor steps) must not count against the caller's budget: the call fits
  ;; in 100 reductions, as it does without native operations.
  (let [nat (c 'data/Nat)
        expensive (app [:const (id 'data/Nat.rec) [[:succ [:zero]]]] [:lam nat nat :explicit] (c 'data/zero)
                       [:lam nat [:lam nat (app (c 'data/succ) (app (c 'data/succ) [:bound 0])) :explicit] :explicit]
                       [:nat 5000])
        term (app (c 'nat/multiply) [:nat 0] expensive)
        with-native (kernel/normalize @env term {:reductions 100})
        without (with-redefs-fn {#'kernel/nat-operations {}} #(kernel/normalize @env term {:reductions 100}))]
    (is (= :normalized (:status without)))
    (is (= :normalized (:status with-native)) (pr-str (:error with-native)))
    (is (= (:term without) (:term with-native)))))
