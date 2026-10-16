(ns rainbow.math.nat.ring-reflect-sound-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.nat.ring-reflect :as r]
            [rainbow.math.nat.ring-reflect-sound :as sound]))

(def ^:private U [:succ [:zero]])
(defn- c [alias] (f/const* alias []))
(defn- ap [g & xs] (apply f/app g xs))
(defn- add [a b] (ap (c 'algebra/nat-add) a b))
(defn- mul [a b] (ap (c 'nat/multiply) a b))
(defn- eqt [T a b] (f/equality U T a b))
(defn- eqn [a b] (eqt r/nat a b))
(defn- refl [T a] (ap (f/const* 'equality/reflexive [U]) T a))
(defn- sym [T a b h] (ap (f/const* 'equality/symmetric [U]) T a b h))
(defn- trans [T a b d h k] (ap (f/const* 'equality/transitive [U]) T a b d h k))
(defn- numeral [n] (nth (iterate #(ap (c 'data/succ) %) r/zero) n))
(def ^:private checked
  (delay
    (let [loaded (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (assert (= :replayed (:status loaded)))
      (sound/extend-environment (:environment loaded)))))
(defn- core [surface]
  (let [result (elaborate/core-expression @checked surface)]
    (assert (= :elaborated (:status result)) (pr-str result))
    (:term result)))
(defn- checks [proof type] (:status (kernel/check @checked (core proof) (core type))))

;; The interface is restated independently of sound/theorem-specs. In particular,
;; no canonicality predicate or ordering premise is permitted in these types.
(def ^:private frozen-statements
  {'ring/eval-pol-mk-px
   (f/forall [['rho r/atom-values] ['p r/pol] ['i r/nat] ['q r/pol]]
             (eqn (r/eval-pol 'rho (r/mk-px 'p 'i 'q))
                  (r/eval-pol 'rho (r/px 'p 'i 'q))))
   'ring/eval-pol-add
   (f/forall [['rho r/atom-values] ['p r/pol] ['q r/pol]]
             (eqn (r/eval-pol 'rho (r/pol-add 'p 'q))
                  (add (r/eval-pol 'rho 'p) (r/eval-pol 'rho 'q))))
   'ring/eval-pol-scale
   (f/forall [['rho r/atom-values] ['k r/nat] ['r r/pol]]
             (eqn (r/eval-pol 'rho (ap (c 'ring/pol-scale) 'k 'r))
                  (mul 'k (r/eval-pol 'rho 'r))))
   'ring/eval-pol-mul-var
   (f/forall [['rho r/atom-values] ['i r/nat] ['r r/pol]]
             (eqn (r/eval-pol 'rho (ap (c 'ring/pol-mul-var) 'i 'r))
                  (mul (r/eval-pol 'rho 'r) (ap 'rho 'i))))
   'ring/eval-pol-mul
   (f/forall [['rho r/atom-values] ['p r/pol] ['q r/pol]]
             (eqn (r/eval-pol 'rho (r/pol-mul 'p 'q))
                  (mul (r/eval-pol 'rho 'p) (r/eval-pol 'rho 'q))))
   'ring/sound
   (f/forall [['rho r/atom-values] ['e r/expr]]
             (eqn (r/denote 'rho 'e) (r/eval-pol 'rho (r/normalize 'e))))
   'ring/pol-equal-sound
   (f/forall [['p r/pol] ['q r/pol]]
             (f/arrow (eqt r/bool (r/pol-equal 'p 'q) (c 'data/true))
                      (eqt r/pol 'p 'q)))
   'ring/identity-sound
   (f/forall [['rho r/atom-values] ['l r/expr] ['rhs r/expr]
              ['same (eqt r/bool (r/pol-equal (r/normalize 'l) (r/normalize 'rhs)) (c 'data/true))]]
     (eqn (r/denote 'rho 'l) (r/denote 'rho 'rhs)))})

(deftest frozen-statements-and-identity-theorem-are-native-axiom-free
  (is (= (set (keys frozen-statements)) (set (keys (sound/theorem-ids @checked)))))
  (doseq [[alias statement] frozen-statements]
    (testing (str alias)
      (let [d (environment/declaration @checked (environment/resolve-id @checked alias))]
        (is (= (core statement) (:rainbow/type d)))
        (is (= :theorem (:rainbow/kind d)))
        (is (= :native (get-in d [:rainbow/provenance :origin])))
        (is (= #{} (kernel/axioms @checked alias))))))
  (doseq [spec sound/algebra-specs]
    (is (= #{} (kernel/axioms @checked (:name spec))))))

(deftest operation-lemmas-accept-noncanonical-polynomials
  (let [z (numeral 0) one (numeral 1) two (numeral 2)
        rho (f/lam [['index r/nat]] (add 'index two))
        polys [(r/pc z) (r/pc (numeral 3))
               ;; A zero coefficient, and variables out of order in both children.
               (r/px (r/pc z) two (r/pc (numeral 4)))
               (r/px (r/px (r/pc one) z (r/pc z)) two
                     (r/px (r/pc two) one (r/pc (numeral 3))))]]
    (doseq [p polys q polys]
      (is (= :checked
             (checks (ap (c 'ring/eval-pol-add) rho p q)
                     (eqn (r/eval-pol rho (r/pol-add p q))
                          (add (r/eval-pol rho p) (r/eval-pol rho q))))))
      (is (= :checked
             (checks (ap (c 'ring/eval-pol-mul) rho p q)
                     (eqn (r/eval-pol rho (r/pol-mul p q))
                          (mul (r/eval-pol rho p) (r/eval-pol rho q)))))))
    (doseq [p polys i [z one two]]
      (is (= :checked
             (checks (ap (c 'ring/eval-pol-mk-px) rho p i (r/pc two))
                     (eqn (r/eval-pol rho (r/mk-px p i (r/pc two)))
                          (r/eval-pol rho (r/px p i (r/pc two)))))))
      (is (= :checked
             (checks (ap (c 'ring/eval-pol-scale) rho i p)
                     (eqn (r/eval-pol rho (ap (c 'ring/pol-scale) i p))
                          (mul i (r/eval-pol rho p))))))
      (is (= :checked
             (checks (ap (c 'ring/eval-pol-mul-var) rho i p)
                     (eqn (r/eval-pol rho (ap (c 'ring/pol-mul-var) i p))
                          (mul (r/eval-pol rho p) (ap rho i)))))))))

(defn- atom-expr [i] (ap (c 'ring/atom) (numeral i)))
(defn- plus [& xs] (reduce #(ap (c 'ring/add) %1 %2) xs))
(defn- times [& xs] (reduce #(ap (c 'ring/mul) %1 %2) xs))

(defn- reflected-proof
  "Build only the theorem applications; no host evaluation certifies equality."
  [l r]
  (let [pl (r/normalize l) pr (r/normalize r)
        dl (r/denote 'rho l) dr (r/denote 'rho r)
        el (r/eval-pol 'rho pl) er (r/eval-pol 'rho pr)
        same (ap (c 'ring/pol-equal-sound) pl pr (refl r/bool (c 'data/true)))
        congruent (ap (f/const* 'equality/congruent-function [U U])
                      r/pol r/nat (f/lam [['poly r/pol]] (r/eval-pol 'rho 'poly)) pl pr same)]
    (f/lam [['rho r/atom-values]]
      (trans r/nat dl el dr (ap (c 'ring/sound) 'rho l)
             (trans r/nat el er dr congruent
                    (sym r/nat dr er (ap (c 'ring/sound) 'rho r)))))))

(deftest reflection-proves-symbolic-identities-and-rejects-forged-certificates
  (let [a (atom-expr 0) b (atom-expr 1) d (atom-expr 2)
        s (plus a b d)
        expanded (apply plus (for [p [a b d] q [a b d] r [a b d]] (times p q r)))
        expected (fn [l r] (f/forall [['rho r/atom-values]]
                                    (eqn (r/denote 'rho l) (r/denote 'rho r))))]
    (doseq [[l r] [[(plus a b) (plus b a)]
                   [(times a (plus b d)) (plus (times a b) (times a d))]
                   [(times s s s) expanded]]]
      (is (= :checked (checks (reflected-proof l r) (expected l r)))))
    (doseq [[l r] [[(plus a b) a]
                   [(times (plus a b) (plus a b)) (plus (times a a) (times b b))]]]
      (is (= :rejected (checks (reflected-proof l r) (expected l r)))))))

(deftest equality-soundness-is-structural-not-equality-at-one-environment
  ;; These polynomials both evaluate to zero in a zero environment, but are
  ;; structurally distinct. A reflexivity token cannot certify pol-equal = true.
  (let [p (r/pc (numeral 0)) q (r/px (r/pc (numeral 0)) (numeral 0) p)]
    (is (= :rejected
           (checks (ap (c 'ring/pol-equal-sound) p q (refl r/bool (c 'data/true)))
                   (eqt r/pol p q))))))

(deftest production-emitter-uses-the-frozen-soundness-interface
  (let [bindings [['a r/nat] ['b r/nat] ['d r/nat]]
        status (fn [l rhs]
                 (checks (f/lam bindings (r/prove-by-reflection l rhs))
                         (f/forall bindings (eqn l rhs))))]
    (doseq [[l rhs] [[(add 'a 'b) (add 'b 'a)]
                     [(mul 'a (add 'b 'd)) (add (mul 'a 'b) (mul 'a 'd))]
                     [(add 'a 'a) (mul [:nat 2] 'a)]
                     [(add [:nat 2] [:nat 3]) [:nat 5]]]]
      (is (= :checked (status l rhs))))
    (is (= :rejected (status (add 'a 'b) 'a)))))

(deftest production-emitter-does-not-capture-user-symbols
  (doseq [name '[ring-table-index ring-table-ignored ring-table-predecessor
                ring-table-result ring-reflect-polynomial ring-reflect-polynomial-0
                ring-table-index-0 ring-table-predecessor-0 ring-table-result-0]
          atom [name (ap 'f name)]]
    (testing (str atom)
      (let [bindings [[name r/nat] ['other r/nat] ['f (f/arrow r/nat r/nat)]]
            lhs (add atom 'other) rhs (add 'other atom)]
        (is (= :checked
               (checks (f/lam bindings (r/prove-by-reflection lhs rhs))
                       (f/forall bindings (eqn lhs rhs)))))
        (is (= :rejected
               (checks (f/lam bindings (r/prove-by-reflection lhs atom))
                       (f/forall bindings (eqn lhs atom)))))))))

(deftest production-emitter-proves-the-symbolic-cubic
  (let [bindings [['a r/nat] ['b r/nat] ['d r/nat]]
        s (add (add 'a 'b) 'd)
        lhs (mul (mul s s) s)
        rhs (reduce add (for [p ['a 'b 'd] q ['a 'b 'd] v ['a 'b 'd]]
                          (mul (mul p q) v)))]
    (is (= :checked
           (checks (f/lam bindings (r/prove-by-reflection lhs rhs))
                   (f/forall bindings (eqn lhs rhs)))))))

(deftest production-emitter-handles-natural-values-beyond-long-range
  (doseq [n [Long/MAX_VALUE 100000000000000000000N]
          successors [1 2]]
    (let [value (nth (iterate #(ap (c 'data/succ) %) [:nat n]) successors)
          lhs (add value [:nat 2])
          rhs [:nat (+' n successors 2)]
          proof (r/prove-by-reflection lhs rhs)]
      (testing (str n " with " successors " successors")
        (is (= :checked (checks proof (eqn lhs rhs)))))
      (is (= :rejected
             (checks proof (eqn lhs (add rhs [:nat 1]))))))))

(deftest production-emitter-keeps-malformed-terms-visible-to-the-checker
  (doseq [bad [[:nat -1] [:nat 1/2] [:nat 1.0] [:nat 1 :extra]
              (ap (c 'data/succ) [:nat -1])
              (ap [:const 'algebra/nat-add [] :extra] [:nat 1] [:nat 2])
              (ap [:const 'nat/multiply [[:zero]]] [:nat 1] [:nat 2])]]
    (testing (pr-str bad)
      (let [candidate (r/prove-by-reflection bad bad)
            elaborated (elaborate/core-expression @checked candidate)
            result (if (= :elaborated (:status elaborated))
                     (kernel/infer @checked (:term elaborated))
                     elaborated)]
        (is (= :rejected (:status result)))))))

(deftest production-emitter-proves-quartic-at-the-default-budget
  (let [bindings [['a r/nat] ['b r/nat] ['d r/nat]]
        variables ['a 'b 'd]
        sum (reduce add variables)
        lhs (reduce mul (repeat 4 sum))
        rhs (reduce add (for [a variables b variables c variables d variables]
                          (reduce mul [a b c d])))
        proof (core (f/lam bindings (r/prove-by-reflection lhs rhs)))
        nodes (count (filter #(and (vector? %) (#{:app :const :bound :lam :pi :let :nat :sort} (first %)))
                             (tree-seq vector? seq proof)))]
    (is (< nodes 3000) "The 81-monomial identity should have a compact certificate")
    (is (= 1000000 kernel/*reduction-budget*) "Exercise the unchanged default")
    (is (= :checked
           (:status (kernel/check @checked proof (core (f/forall bindings (eqn lhs rhs)))))))
    (let [false-rhs (add rhs [:nat 1])
          forged (core (f/lam bindings (r/prove-by-reflection lhs false-rhs)))
          result (kernel/check @checked forged (core (f/forall bindings (eqn lhs false-rhs))))]
      (is (= :rejected (:status result)))
      (is (= :kernel/type-mismatch (get-in result [:error :error/category]))))))
