(ns rainbow.math.nat.ring-reflect-sound
  "Unconditional, native soundness of the nat reflection normalizer.
  All polynomial lemmas quantify over arbitrary Pol, without an ordering or
  nonzero-coefficient assumption. Host helpers only assemble proof terms;
  every supporting lemma and each of the seven interface theorems is checked.
  A derived identity theorem packages their use for compact instance proofs."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.nat.ring-reflect :as r]
            [rainbow.module :as module]))

(def ^:private U [:succ [:zero]])
(def ^:private P [:zero])
(def ^:private N r/nat)
(def ^:private B r/bool)
(def ^:private Pol r/pol)
(def ^:private Expr r/expr)
(def ^:private Env r/atom-values)
(defn- c [a] (f/const* a []))
(defn- ap [g & xs] (apply f/app g xs))
(def ^:private z r/zero)
(def ^:private yes (c 'data/true))
(def ^:private no (c 'data/false))
(defn- add [a b] (ring/nadd a b))
(defn- mul [a b] (ring/nmul a b))
(defn- eqt [T a b] (f/equality U T a b))
(defn- eqn [a b] (eqt N a b))
(defn- refl [T a] (ap (f/const* 'equality/reflexive [U]) T a))
(defn- sym [T a b h] (ap (f/const* 'equality/symmetric [U]) T a b h))
(defn- trans [T a b d h k] (ap (f/const* 'equality/transitive [U]) T a b d h k))
(defn- cong [A T g a b h]
  (ap (f/const* 'equality/congruent-function [U U]) A T g a b h))
(defn- subst [T a b h predicate proof]
  (ap (f/const* 'equality/substitution [U]) T a b h predicate proof))
(defn- step [a b h] {:lhs a :rhs b :proof h})
(defn- chain [& steps]
  (reduce (fn [a b] (step (:lhs a) (:rhs b)
                         (trans N (:lhs a) (:rhs a) (:rhs b) (:proof a) (:proof b)))) steps))
(defn- lift [g s]
  (let [v (gensym "value")]
    (step (g (:lhs s)) (g (:rhs s))
          (cong N N (f/lam [[v N]] (g v)) (:lhs s) (:rhs s) (:proof s)))))
(defn- two [op a b]
  (chain (lift #(op % (:lhs b)) a) (lift #(op (:rhs a) %) b)))
(defn- E [env p] (r/eval-pol env p))
(defn- scale [k p] (ap (c 'ring/pol-scale) k p))
(defn- times-var [i p] (ap (c 'ring/pol-mul-var) i p))
(defn- same [i j] (ap (c 'nat/decide-equality) i j))
(defn- le [i j] (ap (c 'nat/decide-at-most) i j))
(defn- both [a b] (ap (c 'boolean/and) a b))
(defn- choose [b t e]
  (ap (f/const* 'data/Bool.rec [U]) (f/lam [['ignored B]] Pol) e t b))
(defn- nat-same [a b h] (ap (c 'nat/decide-equality-true-sound) a b h))
(defn- impossible [goal h]
  (ap (c 'proposition/explode) goal (ap (c 'bool/false-not-true) h)))

(defn- induct-pol [target goal pc-case px-case]
  (let [v (gensym "poly") n (gensym "coefficient")
        p (gensym "p") hp (gensym "hp") i (gensym "index")
        q (gensym "q") hq (gensym "hq")]
    (ap (f/const* 'ring/Pol.rec [P]) (f/lam [[v Pol]] (goal v))
        (f/lam [[n N]] (pc-case n))
        (f/lam [[p Pol] [hp (goal p)] [i N] [q Pol] [hq (goal q)]]
               (px-case p hp i q hq)) target)))

(defn- cases-bool
  "Split a computed Boolean, retaining decision = branch for soundness lemmas."
  [decision goal false-case true-case]
  (let [b (gensym "decision") h (gensym "case")]
    (ap (f/const* 'data/Bool.rec [P])
        (f/lam [[b B]] (f/arrow (eqt B decision b) (goal b)))
        (f/lam [[h (eqt B decision no)]] (false-case h))
        (f/lam [[h (eqt B decision yes)]] (true-case h))
        decision (refl B decision))))

(defn- theorem [name bindings goal proof]
  {:name name :universes [] :type (f/forall bindings goal) :value (f/lam bindings proof)})

;; Small fixed algebra lemmas are proved once, not emitted for each reflected goal.
(defn- algebra-law [name names lhs rhs]
  (theorem name (mapv #(vector % N) names) (eqn lhs rhs)
           (:proof (ring/prove-nat-eq lhs rhs))))

(def algebra-specs
  [(algebra-law 'ring/add-constant-law '[a b d]
                (add 'b (add 'a 'd)) (add 'a (add 'b 'd)))
   (algebra-law 'ring/add-tail-law '[a b d]
                (add 'a (add 'b 'd)) (add (add 'a 'b) 'd))
   (algebra-law 'ring/add-same-index-law '[a b x d e]
                (add (mul (add 'a 'b) 'x) (add 'd 'e))
                (add (add (mul 'a 'x) 'd) (add (mul 'b 'x) 'e)))
   (algebra-law 'ring/scale-horner-law '[k a x b]
                (add (mul (mul 'k 'a) 'x) (mul 'k 'b))
                (mul 'k (add (mul 'a 'x) 'b)))
   (algebra-law 'ring/multiply-horner-law '[a x b k]
                (add (mul (mul 'a 'k) 'x) (mul 'b 'k))
                (mul (add (mul 'a 'x) 'b) 'k))])

(def eval-pol-mk-px-spec
  (let [goal (fn [p] (f/forall [['i N] ['q Pol]]
                              (eqn (E 'env (r/mk-px p 'i 'q)) (E 'env (r/px p 'i 'q)))))]
    (theorem 'ring/eval-pol-mk-px [['env Env] ['p Pol]] (goal 'p)
      (induct-pol 'p goal
        (fn [a]
          (f/lam [['i N] ['q Pol]]
            (let [rhs (add (mul a (ap 'env 'i)) (E 'env 'q))]
              (cases-bool (same a z)
                #(eqn (E 'env (choose % 'q (r/px (r/pc a) 'i 'q))) rhs)
                (fn [_] (refl N rhs))
                (fn [h]
                  (sym N rhs (E 'env 'q)
                       (:proof (lift #(add (mul % (ap 'env 'i)) (E 'env 'q))
                                     (step a z (nat-same a z h))))))))))
        (fn [p _ i q _]
          (f/lam [['j N] ['rest Pol]]
            (refl N (E 'env (r/px (r/px p i q) 'j 'rest)))))))))

(defn- mk-step [env p i q]
  (step (E env (r/mk-px p i q)) (add (mul (E env p) (ap env i)) (E env q))
        (ap (c 'ring/eval-pol-mk-px) env p i q)))

(defn- horner-cong [env i a b]
  (two add (lift #(mul % (ap env i)) a) b))

(def eval-pol-add-spec
  (let [goal (fn [p q] (eqn (E 'env (r/pol-add p q)) (add (E 'env p) (E 'env q))))
        outer (fn [p] (f/forall [['right Pol]] (goal p 'right)))]
    (theorem 'ring/eval-pol-add [['env Env] ['p Pol]] (outer 'p)
      (induct-pol 'p outer
        (fn [a]
          (f/lam [['right Pol]]
            (induct-pol 'right #(goal (r/pc a) %)
              (fn [b] (refl N (add a b)))
              (fn [p _ j q hq]
                (let [tail (step (E 'env (r/pol-add (r/pc a) q))
                                 (add a (E 'env q)) hq)
                      lhs (add (mul (E 'env p) (ap 'env j)) (add a (E 'env q)))
                      rhs (add a (E 'env (r/px p j q)))]
                  (:proof (chain (lift #(add (mul (E 'env p) (ap 'env j)) %) tail)
                                 (step lhs rhs (ap (c 'ring/add-constant-law)
                                                   a (mul (E 'env p) (ap 'env j)) (E 'env q))))))))))
        (fn [p hp i q hq]
          (let [left (r/px p i q)
                tail-case
                (fn [right]
                  (let [s (lift #(add (mul (E 'env p) (ap 'env i)) %)
                                (step (E 'env (r/pol-add q right))
                                      (add (E 'env q) (E 'env right)) (ap hq right)))]
                    (:proof (chain s
                              (step (:rhs s) (add (E 'env left) (E 'env right))
                                    (ap (c 'ring/add-tail-law) (mul (E 'env p) (ap 'env i))
                                        (E 'env q) (E 'env right)))))))]
            (f/lam [['right Pol]]
              (induct-pol 'right #(goal left %)
                (fn [b] (tail-case (r/pc b)))
                (fn [p2 _ j q2 hq2]
                  (let [right (r/px p2 j q2)
                        merged (r/px (r/pol-add p p2) i (r/pol-add q q2))
                        below (r/px p i (r/pol-add q right))
                        above (r/px p2 j (r/pol-add left q2))
                        rhs (add (E 'env left) (E 'env right))]
                    (cases-bool (same i j)
                      #(eqn (E 'env (choose % merged (choose (le i j) below above))) rhs)
                      (fn [_]
                        (cases-bool (le i j) #(eqn (E 'env (choose % below above)) rhs)
                          (fn [_]
                            (let [s (lift #(add (mul (E 'env p2) (ap 'env j)) %)
                                          (step (E 'env (r/pol-add left q2))
                                                (add (E 'env left) (E 'env q2)) hq2))]
                              (:proof (chain s
                                        (step (:rhs s) rhs (ap (c 'ring/add-constant-law)
                                                              (E 'env left) (mul (E 'env p2) (ap 'env j))
                                                              (E 'env q2)))))))
                          (fn [_] (tail-case right))))
                      (fn [same-index]
                        (let [s (horner-cong 'env i
                                  (step (E 'env (r/pol-add p p2)) (add (E 'env p) (E 'env p2)) (ap hp p2))
                                  (step (E 'env (r/pol-add q q2)) (add (E 'env q) (E 'env q2)) (ap hq q2)))
                              at-i (:proof (chain s
                                             (step (:rhs s) (add (E 'env left) (E 'env (r/px p2 i q2)))
                                                   (ap (c 'ring/add-same-index-law)
                                                       (E 'env p) (E 'env p2) (ap 'env i) (E 'env q) (E 'env q2)))))
                              v (gensym "index")]
                          (subst N i j (nat-same i j same-index)
                                 (f/lam [[v N]] (eqn (E 'env merged)
                                                    (add (E 'env left) (E 'env (r/px p2 v q2)))))
                                 at-i))))))))))))))

(def eval-pol-scale-spec
  (let [goal #(eqn (E 'env (scale 'k %)) (mul 'k (E 'env %)))]
    (theorem 'ring/eval-pol-scale [['env Env] ['k N] ['r Pol]] (goal 'r)
      (induct-pol 'r goal
        (fn [a] (refl N (mul 'k a)))
        (fn [p hp i q hq]
          (let [s (chain (mk-step 'env (scale 'k p) i (scale 'k q))
                         (horner-cong 'env i
                           (step (E 'env (scale 'k p)) (mul 'k (E 'env p)) hp)
                           (step (E 'env (scale 'k q)) (mul 'k (E 'env q)) hq)))]
            (:proof (chain s
                      (step (:rhs s) (mul 'k (E 'env (r/px p i q)))
                            (ap (c 'ring/scale-horner-law) 'k (E 'env p) (ap 'env i) (E 'env q)))))))))))

(defn- wrap-variable [env i p]
  (let [s (mk-step env p i (r/pc z))
        product (mul (E env p) (ap env i))]
    (chain s (step (:rhs s) product (ap (c 'algebra/nat-add-zero-right) product)))))

(def eval-pol-mul-var-spec
  (let [goal #(eqn (E 'env (times-var 'i %)) (mul (E 'env %) (ap 'env 'i)))]
    (theorem 'ring/eval-pol-mul-var [['env Env] ['i N] ['r Pol]] (goal 'r)
      (induct-pol 'r goal
        (fn [a] (:proof (wrap-variable 'env 'i (r/pc a))))
        (fn [p hp j q hq]
          (let [poly (r/px p j q)
                wrap (r/mk-px poly 'i (r/pc z))
                inside (r/mk-px (times-var 'i p) j (times-var 'i q))
                rhs (mul (E 'env poly) (ap 'env 'i))]
            (cases-bool (same j 'i)
              #(eqn (E 'env (choose % wrap (choose (le j 'i) inside wrap))) rhs)
              (fn [_]
                (cases-bool (le j 'i) #(eqn (E 'env (choose % inside wrap)) rhs)
                  (fn [_] (:proof (wrap-variable 'env 'i poly)))
                  (fn [_]
                    (let [s (chain (mk-step 'env (times-var 'i p) j (times-var 'i q))
                                   (horner-cong 'env j
                                     (step (E 'env (times-var 'i p)) (mul (E 'env p) (ap 'env 'i)) hp)
                                     (step (E 'env (times-var 'i q)) (mul (E 'env q) (ap 'env 'i)) hq)))]
                      (:proof (chain s (step (:rhs s) rhs
                                             (ap (c 'ring/multiply-horner-law)
                                                 (E 'env p) (ap 'env j) (E 'env q) (ap 'env 'i)))))))))
              (fn [_] (:proof (wrap-variable 'env 'i poly))))))))))

(def eval-pol-mul-spec
  (let [goal #(eqn (E 'env (r/pol-mul % 'q)) (mul (E 'env %) (E 'env 'q)))]
    (theorem 'ring/eval-pol-mul [['env Env] ['p Pol] ['q Pol]] (goal 'p)
      (induct-pol 'p goal
        (fn [k] (ap (c 'ring/eval-pol-scale) 'env k 'q))
        (fn [p hp i rest hrest]
          (let [a (r/pol-mul p 'q) b (r/pol-mul rest 'q)
                s (chain
                    (step (E 'env (r/pol-add (times-var i a) b))
                          (add (E 'env (times-var i a)) (E 'env b))
                          (ap (c 'ring/eval-pol-add) 'env (times-var i a) b))
                    (two add
                      (chain (step (E 'env (times-var i a)) (mul (E 'env a) (ap 'env i))
                                   (ap (c 'ring/eval-pol-mul-var) 'env i a))
                             (lift #(mul % (ap 'env i))
                                   (step (E 'env a) (mul (E 'env p) (E 'env 'q)) hp)))
                      (step (E 'env b) (mul (E 'env rest) (E 'env 'q)) hrest)))]
            (:proof (chain s (step (:rhs s) (mul (E 'env (r/px p i rest)) (E 'env 'q))
                                   (ap (c 'ring/multiply-horner-law)
                                       (E 'env p) (ap 'env i) (E 'env rest) (E 'env 'q)))))))))))

(def sound-spec
  (let [goal #(eqn (r/denote 'env %) (E 'env (r/normalize %)))
        binary-case
        (fn [constructor op lemma]
          (f/lam [['a Expr] ['ha (goal 'a)] ['b Expr] ['hb (goal 'b)]]
            (let [na (r/normalize 'a) nb (r/normalize 'b)
                  s (two op (step (r/denote 'env 'a) (E 'env na) 'ha)
                            (step (r/denote 'env 'b) (E 'env nb) 'hb))
                  finish (E 'env (r/normalize (ap (c constructor) 'a 'b)))]
              (:proof (chain s (step (:rhs s) finish
                                     (sym N finish (:rhs s) (ap (c lemma) 'env na nb))))))))]
    (theorem 'ring/sound [['env Env] ['e Expr]] (goal 'e)
      (ap (f/const* 'ring/Expr.rec [P]) (f/lam [['node Expr]] (goal 'node))
          (f/lam [['i N]]
            (let [s (wrap-variable 'env 'i (r/pc r/one))
                  x (ap 'env 'i)
                  finish (chain s (step (:rhs s) x (ap (c 'algebra/nat-add-zero-right) x)))]
              (sym N (:lhs finish) x (:proof finish))))
          (f/lam [['a N]] (refl N 'a))
          (binary-case 'ring/add add 'ring/eval-pol-add)
          (binary-case 'ring/mul mul 'ring/eval-pol-mul) 'e))))

(def pol-equal-sound-spec
  (let [goal (fn [p q] (f/arrow (eqt B (r/pol-equal p q) yes) (eqt Pol p q)))
        outer #(f/forall [['right Pol]] (goal % 'right))
        mismatch (fn [p q] (f/lam [['h (eqt B no yes)]] (impossible (eqt Pol p q) 'h)))]
    (theorem 'ring/pol-equal-sound [['p Pol]] (outer 'p)
      (induct-pol 'p outer
        (fn [a]
          (f/lam [['right Pol]]
            (induct-pol 'right #(goal (r/pc a) %)
              (fn [b]
                (f/lam [['h (eqt B (same a b) yes)]]
                  (cong N Pol (c 'ring/pc) a b (nat-same a b 'h))))
              (fn [p _ i q _] (mismatch (r/pc a) (r/px p i q))))))
        (fn [p hp i q hq]
          (let [left (r/px p i q)]
            (f/lam [['right Pol]]
              (induct-pol 'right #(goal left %)
                (fn [b] (mismatch left (r/pc b)))
                (fn [p2 _ j q2 _]
                  (let [ep (r/pol-equal p p2) eq (r/pol-equal q q2)
                        ij (same i j) children (both ep eq)
                        left-of #(ap (c 'boolean/and-implies-left) %1 %2 %3)
                        right-of #(ap (c 'boolean/and-implies-right) %1 %2 %3)
                        hc (right-of ij children 'h)
                        p-proof (ap hp p2 (left-of ep eq hc))
                        i-proof (nat-same i j (left-of ij children 'h))
                        q-proof (ap hq q2 (right-of ep eq hc))
                        v (gensym "replace")
                        mid1 (r/px p2 i q) mid2 (r/px p2 j q) right (r/px p2 j q2)]
                    (f/lam [['h (eqt B (both ij children) yes)]]
                      (trans Pol left mid1 right
                        (cong Pol Pol (f/lam [[v Pol]] (r/px v i q)) p p2 p-proof)
                        (trans Pol mid1 mid2 right
                          (cong N Pol (f/lam [[v N]] (r/px p2 v q)) i j i-proof)
                          (cong Pol Pol (f/lam [[v Pol]] (r/px p2 j v)) q q2 q-proof))))))))))))))

(def identity-sound-spec
  (let [left (r/normalize 'left) right (r/normalize 'right)
        dl (r/denote 'env 'left) dr (r/denote 'env 'right)
        el (E 'env left) er (E 'env right)]
    (theorem 'ring/identity-sound
      [['env Env] ['left Expr] ['right Expr]
       ['checked (eqt B (r/pol-equal left right) yes)]]
      (eqn dl dr)
      (trans N dl el dr
        (ap (c 'ring/sound) 'env 'left)
        (trans N el er dr
          (cong Pol N (f/lam [['polynomial Pol]] (E 'env 'polynomial))
                left right (ap (c 'ring/pol-equal-sound) left right 'checked))
          (sym N dr er (ap (c 'ring/sound) 'env 'right)))))))

(def theorem-specs
  [eval-pol-mk-px-spec eval-pol-add-spec eval-pol-scale-spec eval-pol-mul-var-spec
   eval-pol-mul-spec sound-spec pol-equal-sound-spec identity-sound-spec])
(def deps '[rainbow.math.nat.ring-reflect rainbow.math.nat.semiring])
(defn install [checked-environment]
  (support/extend-with checked-environment :nat-ring-reflect-sound
                       (concat algebra-specs theorem-specs)))
(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.ring-reflect-sound))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
