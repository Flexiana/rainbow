(ns rainbow.math.nat.ring-reflect
  "Definitions for proving nat semiring identities BY REFLECTION.

  `rainbow.math.nat.ring` proves an identity by emitting a rewrite chain, and the
  chain grows super-linearly with the degree: (a+b+c)^3 takes 914,191 term nodes
  over nnrat. Reflection moves that work into one kernel computation instead. A goal
  is reified as a `ring/Expr`, both sides are normalized to Horner polynomials
  (`ring/Pol`) by `ring/normalize`, and `ring/pol-equal` compares the two normal
  forms; one soundness theorem, proved once, turns `pol-equal ... = true` into the
  equality of the original sides. The per-goal proof is then the size of the reified
  goal, and the kernel computes the normal forms (natively, on numeral literals).

  This module holds only the definitions. The soundness theorems
  (`ring/eval-pol-add`, `ring/eval-pol-mul`, `ring/sound`, `ring/pol-equal-sound`)
  are stated in WORKPLAN-2026-10-15-reflection.md and live in their own module.

  Normal form. `px p i q` denotes p * x_i + q. A polynomial is canonical when, in
  every `px p i q`, p is not `pc 0`, every index in p is >= i and every index in q
  is > i; `mk-px` keeps the first condition, and the operations keep the others when
  their inputs are canonical. Canonical forms of equal polynomials are equal, so
  `pol-equal` decides the identity. Soundness does not depend on canonicity: on any
  input the operations denote addition and multiplication, so a non-canonical input
  can make the tactic fail, never make it prove something false.

  Addition retains an equal-index px without testing its summed coefficient:
  canonical Nat coefficients cannot cancel. On non-canonical inputs this can
  retain a zero coefficient; the unconditional denotation law still holds.

  Native and axiom-free."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def expr (function/const* 'ring/Expr []))
(def pol (function/const* 'ring/Pol []))
(def atom-values (function/arrow nat nat))

(defn- app [f & args] (apply function/app f args))
(defn- c [alias] (function/const* alias []))
(defn- lam [bindings body] (function/lam bindings body))

(def zero (c 'data/zero))
(defn- succ [n] (app (c 'data/succ) n))
(def one (succ zero))

(defn- nadd [a b] (app (c 'algebra/nat-add) a b))
(defn- nmul [a b] (app (c 'nat/multiply) a b))
(defn- same? [a b] (app (c 'nat/decide-equality) a b))
(defn- at-most? [a b] (app (c 'nat/decide-at-most) a b))
(defn- both [a b] (app (c 'boolean/and) a b))

(defn- choose
  "if b then t else e, at type T"
  [T b t e]
  (app (function/const* 'data/Bool.rec [type-level]) (lam [['decided bool]] T) e t b))

(defn- pol-rec [motive pc-case px-case target]
  (app (function/const* 'ring/Pol.rec [type-level]) motive pc-case px-case target))
(defn- expr-rec [motive atom-case const-case add-case mul-case target]
  (app (function/const* 'ring/Expr.rec [type-level]) motive atom-case const-case add-case mul-case target))

(defn pc [n] (app (c 'ring/pc) n))
(defn px [p i q] (app (c 'ring/px) p i q))
(defn mk-px [p i q] (app (c 'ring/mk-px) p i q))
(defn pol-add [p q] (app (c 'ring/pol-add) p q))
(defn pol-mul [p q] (app (c 'ring/pol-mul) p q))
(defn eval-pol [env p] (app (c 'ring/eval-pol) env p))
(defn normalize [e] (app (c 'ring/normalize) e))
(defn denote [env e] (app (c 'ring/denote) env e))
(defn pol-equal [p q] (app (c 'ring/pol-equal) p q))

;; ---- the two inductive types ---------------------------------------------------

(defn- core [checked-environment alias]
  (let [id (environment/resolve-id checked-environment alias)]
    (when-not id (throw (ex-info "ring blocks need a declaration the environment lacks" {:alias alias})))
    [:const id []]))

(defn expr-spec [checked-environment]
  (let [core-nat (core checked-environment 'data/Nat)]
    {:block/schema-version 1 :block/alias 'ring/Expr :block/universes [] :block/parameters []
     :block/sort-level type-level
     :block/constructors
     [{:constructor/alias 'ring/atom :constructor/fields [{:field/name 'index :field/type core-nat}]}
      {:constructor/alias 'ring/const :constructor/fields [{:field/name 'value :field/type core-nat}]}
      {:constructor/alias 'ring/add :constructor/fields [{:field/name 'left :field/type [:self]}
                                                         {:field/name 'right :field/type [:self]}]}
      {:constructor/alias 'ring/mul :constructor/fields [{:field/name 'left :field/type [:self]}
                                                         {:field/name 'right :field/type [:self]}]}]}))

(defn pol-spec [checked-environment]
  (let [core-nat (core checked-environment 'data/Nat)]
    {:block/schema-version 1 :block/alias 'ring/Pol :block/universes [] :block/parameters []
     :block/sort-level type-level
     :block/constructors
     [{:constructor/alias 'ring/pc :constructor/fields [{:field/name 'value :field/type core-nat}]}
      {:constructor/alias 'ring/px :constructor/fields [{:field/name 'coefficient :field/type [:self]}
                                                        {:field/name 'index :field/type core-nat}
                                                        {:field/name 'rest :field/type [:self]}]}]}))

;; ---- definitions ----------------------------------------------------------------

(defn- definition [alias type value]
  {:name alias :kind :definition :universes [] :transparency :reducible :type type :value value})

(def is-zero-pc-spec
  (definition 'ring/is-zero-pc (function/arrow pol bool)
    (lam [['p pol]]
         (pol-rec (lam [['ignored pol]] bool)
                  (lam [['value nat]] (same? 'value zero))
                  (lam [['coefficient pol] ['coefficient-zero bool] ['index nat] ['rest pol] ['rest-zero bool]]
                       (c 'data/false))
                  'p))))

(def mk-px-spec
  ;; px p i q, except that 0 * x_i + q is q
  (definition 'ring/mk-px (function/arrow pol nat pol pol)
    (lam [['p pol] ['i nat] ['q pol]]
         (choose pol (app (c 'ring/is-zero-pc) 'p) 'q (px 'p 'i 'q)))))

(def eval-pol-spec
  (definition 'ring/eval-pol (function/arrow atom-values pol nat)
    (lam [['env atom-values] ['p pol]]
         (pol-rec (lam [['ignored pol]] nat)
                  (lam [['value nat]] 'value)
                  (lam [['coefficient pol] ['coefficient-value nat] ['index nat] ['rest pol] ['rest-value nat]]
                       (nadd (nmul 'coefficient-value (app 'env 'index)) 'rest-value))
                  'p))))

(def pol-add-spec
  ;; By recursion on the left polynomial, and inside it on the right one: every call
  ;; is on a structurally smaller left argument, or on the same left argument and a
  ;; smaller right one.
  (definition 'ring/pol-add (function/arrow pol pol pol)
    (lam [['left pol]]
         (pol-rec (lam [['ignored pol]] (function/arrow pol pol))
                  (lam [['a nat]]
                       (lam [['right pol]]
                            (pol-rec (lam [['ignored pol]] pol)
                                     (lam [['b nat]] (pc (nadd 'a 'b)))
                                     (lam [['p2 pol] ['p2-sum pol] ['j nat] ['q2 pol] ['q2-sum pol]]
                                          (px 'p2 'j 'q2-sum))
                                     'right)))
                  (lam [['p pol] ['add-p (function/arrow pol pol)] ['i nat]
                        ['q pol] ['add-q (function/arrow pol pol)]]
                       (lam [['right pol]]
                            (pol-rec (lam [['ignored pol]] pol)
                                     (lam [['b nat]] (px 'p 'i (app 'add-q (pc 'b))))
                                     (lam [['p2 pol] ['left-plus-p2 pol] ['j nat] ['q2 pol] ['left-plus-q2 pol]]
                                          (choose pol (same? 'i 'j)
                                                  ;; Canonical coefficients are nonzero, and addition
                                                  ;; over Nat cannot cancel them. Avoid inspecting the
                                                  ;; recursive sum before retaining it: under lazy
                                                  ;; reduction that repeats the prefix computation.
                                                  (px (app 'add-p 'p2) 'i (app 'add-q 'q2))
                                                  (choose pol (at-most? 'i 'j)
                                                          ;; i < j: the right side belongs in the rest
                                                          (px 'p 'i (app 'add-q (px 'p2 'j 'q2)))
                                                          ;; j < i: the left side belongs in the right's rest
                                                          (px 'p2 'j 'left-plus-q2))))
                                     'right)))
                  'left))))

(def pol-scale-spec
  (definition 'ring/pol-scale (function/arrow nat pol pol)
    (lam [['k nat] ['r pol]]
         (pol-rec (lam [['ignored pol]] pol)
                  (lam [['value nat]] (pc (nmul 'k 'value)))
                  (lam [['coefficient pol] ['scaled-coefficient pol] ['index nat] ['rest pol] ['scaled-rest pol]]
                       (mk-px 'scaled-coefficient 'index 'scaled-rest))
                  'r))))

(def pol-mul-var-spec
  ;; r * x_i, keeping the variable order
  (definition 'ring/pol-mul-var (function/arrow nat pol pol)
    (lam [['i nat] ['r pol]]
         (pol-rec (lam [['ignored pol]] pol)
                  (lam [['value nat]] (mk-px (pc 'value) 'i (pc zero)))
                  (lam [['p pol] ['p-times pol] ['j nat] ['q pol] ['q-times pol]]
                       (choose pol (same? 'j 'i)
                               (mk-px (px 'p 'j 'q) 'i (pc zero))
                               (choose pol (at-most? 'j 'i)
                                       ;; j < i: (p x_j + q) x_i = (p x_i) x_j + q x_i
                                       (mk-px 'p-times 'j 'q-times)
                                       ;; j > i: every index of r is above i
                                       (mk-px (px 'p 'j 'q) 'i (pc zero)))))
                  'r))))

(def pol-mul-spec
  ;; mul (pc k) r = scale k r ; mul (px p i q) r = (p r) x_i + q r
  (definition 'ring/pol-mul (function/arrow pol pol pol)
    (lam [['left pol] ['right pol]]
         (pol-rec (lam [['ignored pol]] pol)
                  (lam [['k nat]] (app (c 'ring/pol-scale) 'k 'right))
                  (lam [['p pol] ['p-times pol] ['i nat] ['q pol] ['q-times pol]]
                       (pol-add (app (c 'ring/pol-mul-var) 'i 'p-times) 'q-times))
                  'left))))

(def normalize-spec
  (definition 'ring/normalize (function/arrow expr pol)
    (lam [['e expr]]
         (expr-rec (lam [['ignored expr]] pol)
                   (lam [['index nat]] (mk-px (pc one) 'index (pc zero)))
                   (lam [['value nat]] (pc 'value))
                   (lam [['a expr] ['a-normal pol] ['b expr] ['b-normal pol]] (pol-add 'a-normal 'b-normal))
                   (lam [['a expr] ['a-normal pol] ['b expr] ['b-normal pol]] (pol-mul 'a-normal 'b-normal))
                   'e))))

(def denote-spec
  (definition 'ring/denote (function/arrow atom-values expr nat)
    (lam [['env atom-values] ['e expr]]
         (expr-rec (lam [['ignored expr]] nat)
                   (lam [['index nat]] (app 'env 'index))
                   (lam [['value nat]] 'value)
                   (lam [['a expr] ['a-value nat] ['b expr] ['b-value nat]] (nadd 'a-value 'b-value))
                   (lam [['a expr] ['a-value nat] ['b expr] ['b-value nat]] (nmul 'a-value 'b-value))
                   'e))))

(def pol-equal-spec
  (definition 'ring/pol-equal (function/arrow pol pol bool)
    (lam [['left pol]]
         (pol-rec (lam [['ignored pol]] (function/arrow pol bool))
                  (lam [['a nat]]
                       (lam [['right pol]]
                            (pol-rec (lam [['ignored pol]] bool)
                                     (lam [['b nat]] (same? 'a 'b))
                                     (lam [['p2 pol] ['x bool] ['j nat] ['q2 pol] ['y bool]] (c 'data/false))
                                     'right)))
                  (lam [['p pol] ['equal-p (function/arrow pol bool)] ['i nat]
                        ['q pol] ['equal-q (function/arrow pol bool)]]
                       (lam [['right pol]]
                            (pol-rec (lam [['ignored pol]] bool)
                                     (lam [['b nat]] (c 'data/false))
                                     (lam [['p2 pol] ['x bool] ['j nat] ['q2 pol] ['y bool]]
                                          (both (same? 'i 'j) (both (app 'equal-p 'p2) (app 'equal-q 'q2))))
                                     'right)))
                  'left))))

(def definition-specs
  [is-zero-pc-spec mk-px-spec eval-pol-spec pol-add-spec pol-scale-spec pol-mul-var-spec
   pol-mul-spec normalize-spec denote-spec pol-equal-spec])

(defn- install-blocks [checked-environment]
  (reduce (fn [env [alias spec-fn]]
            (if (environment/resolve-id env alias)
              env
              (let [added (kernel/add-inductive-block env (spec-fn env))]
                (when-not (= :accepted (:status added))
                  (throw (ex-info "ring inductive block was rejected" {:alias alias :result added})))
                (:environment added))))
          checked-environment
          [['ring/Expr expr-spec] ['ring/Pol pol-spec]]))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.logic.boolean-and rainbow.math.nat.linear-order rainbow.math.linear.matrix.row-length-decider
    rainbow.math.finite.expectation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment install-blocks (support/extend-with :nat-ring-reflect definition-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.ring-reflect))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

;; ---- the tactic: reify a goal and emit a reflective proof -------------------------
;; The emitter is untrusted: it builds a candidate proof term, and the kernel decides.
;; It needs `ring/identity-sound` from nat-ring-reflect-sound installed.

(defn- operation [t]
  ;; Flat surface application [:app [:const alias []] l r]. Keep malformed
  ;; heads as atoms, so the elaborator/kernel sees the original input.
  (when (and (vector? t) (= :app (first t)) (= 4 (count t)))
    (cond (= (second t) (c 'algebra/nat-add)) :add
          (= (second t) (c 'nat/multiply)) :mul)))

(defn- numeral [t]
  (loop [t t n 0]
    (cond (= t (c 'data/zero)) n
          (and (vector? t) (= :app (first t)) (= 3 (count t)) (= (second t) (c 'data/succ))) (recur (nth t 2) (inc' n))
          (and (vector? t) (= :nat (first t)) (= 2 (count t))
               (integer? (second t)) (not (neg? (second t)))) (+' n (second t))
          :else nil)))

(defn reify
  "[expression atoms]: l as a ring/Expr over atoms (a vector of the subterms that are
  neither sums, products nor numerals, each once, in order of appearance)."
  ([t] (reify t []))
  ([t atoms]
   (if-let [op (operation t)]
     (let [[a atoms] (reify (nth t 2) atoms)
           [b atoms] (reify (nth t 3) atoms)]
       [(app (c (if (= :add op) 'ring/add 'ring/mul)) a b) atoms])
     (if-let [n (numeral t)]
       [(app (c 'ring/const) [:nat n]) atoms]
       (let [i (or (first (keep-indexed #(when (= %2 t) %1) atoms)) (count atoms))]
         [(app (c 'ring/atom) [:nat i]) (if (< i (count atoms)) atoms (conj atoms t))])))))

(defn- fresh-binder [terms prefix]
  ;; Avoid every input symbol, including those inside compound atoms. Merely
  ;; choosing an uncommon name (or calling gensym) can collide with user input.
  (let [used (into #{} (filter symbol?) (tree-seq coll? seq terms))]
    (first (remove used (map #(symbol (str prefix "-" %)) (range))))))

(defn atom-table
  "fun i => the i-th atom (the last one for every later index), as Nat.rec on i.
  Generated binders avoid all symbols in the atoms, preserving user variables."
  [atoms]
  (let [index (fresh-binder atoms "ring-table-index")
        ignored (fresh-binder atoms "ring-table-ignored")
        predecessor (fresh-binder atoms "ring-table-predecessor")
        result (fresh-binder atoms "ring-table-result")]
    (reduce (fn [table value]
              (lam [[index nat]]
                   (app (function/const* 'data/Nat.rec [type-level])
                        (lam [[ignored nat]] nat)
                        value
                        (lam [[predecessor nat] [result nat]]
                             (app table predecessor))
                        index)))
            (lam [[index nat]] (last atoms))
            (reverse (butlast atoms)))))

(defn prove-by-reflection
  "Emit a candidate proof of (equality Nat lhs rhs). The kernel must check it;
  unequal normal forms produce a candidate that the kernel rejects."
  [lhs rhs]
  (let [[el atoms] (reify lhs)
        [er atoms] (reify rhs atoms)
        atoms (if (seq atoms) atoms [(c 'data/zero)])
        env (atom-table atoms)]
    (app (c 'ring/identity-sound) env el er
         (app (function/const* 'equality/reflexive [type-level]) bool (c 'data/true)))))
