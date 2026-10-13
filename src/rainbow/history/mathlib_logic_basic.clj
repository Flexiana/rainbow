(ns rainbow.history.mathlib-logic-basic
  "Proof-hidden Mathlib Logic.Basic stroke with dependency-aware selection."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-unique-existence-transport :as mathlib-unique-existence-transport]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.quantifier :as quantifier]
            [rainbow.term :as term]))

(def report-path "artifacts/day32/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day32-statements.edn")
(def source-path "Mathlib/Logic/Basic.lean")

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])

(def arrow function/arrow)
(def forall function/forall)
(def lam function/lam)
(def app function/app)
(def const* function/const*)

(defn truth [] (proposition/truth))
(defn falsity [] (proposition/falsity))
(defn negation [value] (proposition/negation value))
(defn conjunction [left right] (proposition/conjunction left right))
(defn disjunction [left right] (proposition/disjunction left right))
(defn equivalence [left right] (proposition/equivalence left right))

(defn conjoin [left right left-evidence right-evidence]
  (app (const* 'proposition/conjoin [])
       left right left-evidence right-evidence))

(defn conjunction-left [left right evidence]
  (app (const* 'proposition/left []) left right evidence))

(defn conjunction-right [left right evidence]
  (app (const* 'proposition/right []) left right evidence))

(defn iff-forward [left right evidence]
  (conjunction-left (arrow left right) (arrow right left) evidence))

(defn iff-backward [left right evidence]
  (conjunction-right (arrow left right) (arrow right left) evidence))

(defn left-disjunct [left right evidence]
  (app (const* 'proposition/left-disjunct []) left right evidence))

(defn right-disjunct [left right evidence]
  (app (const* 'proposition/right-disjunct []) left right evidence))

(defn use-disjunction [left right result evidence on-left on-right]
  (app (const* 'proposition/use-disjunction [])
       left right result evidence on-left on-right))

(defn witness [level carrier predicate value evidence]
  (app (const* 'proposition/witness [level])
       carrier predicate value evidence))

(defn use-witness [level carrier predicate result evidence continue]
  (app (const* 'proposition/use-witness [level])
       carrier predicate result evidence continue))

(defn trivial []
  (const* 'proposition/trivial []))

(defn dependent-carriers [arity]
  (cond
    (= 1 arity)
    {:universes ['u]
       :outer [['A sort-u]]
       :arguments [['x 'A]]}

    (= 2 arity)
    {:universes ['u 'v]
       :outer [['A sort-u]
               ['B (forall [['x 'A]] sort-v)]]
       :arguments [['x 'A] ['y (app 'B 'x)]]}

    (= 3 arity)
    {:universes ['u 'v 'w]
       :outer [['A sort-u]
               ['B (forall [['x 'A]] sort-v)]
               ['C (forall [['x 'A] ['y (app 'B 'x)]] sort-w)]]
       :arguments [['x 'A]
                   ['y (app 'B 'x)]
                   ['z (app 'C 'x 'y)]]}

    :else
    (throw (ex-info "Unsupported dependent carrier arity"
                    {:arity arity}))))

(defn argument-names [bindings]
  (mapv first bindings))

(defn nested-implication-spec [arity]
  (let [{:keys [universes outer arguments]} (dependent-carriers arity)
        names (argument-names arguments)
        predicate-type (quantifier/nested-forall arguments 'Prop)
        source (apply app 'P names)
        target (apply app 'Q names)
        all-source (quantifier/nested-forall arguments source)
        all-target (quantifier/nested-forall arguments target)]
    {:name (symbol "logic" (str "forall-" arity "-implication"))
     :foreign/names [(get {2 "forall₂_imp" 3 "forall₃_imp"} arity)]
     :universes universes
     :type
     (forall (vec (concat outer
                          [['P predicate-type]
                           ['Q predicate-type]
                           ['pointwise
                            (quantifier/nested-forall
                             arguments (arrow source target))]
                           ['all-source all-source]]))
             all-target)
     :value
     (lam (vec (concat outer
                       [['P predicate-type]
                        ['Q predicate-type]
                        ['pointwise
                         (quantifier/nested-forall
                          arguments (arrow source target))]
                        ['all-source all-source]]
                       arguments))
          (apply app 'pointwise
                 (concat names [(apply app 'all-source names)])))}))

(defn forall-truth-spec [arity]
  (let [{:keys [universes outer arguments]} (dependent-carriers arity)
        all-truth (quantifier/nested-forall arguments (truth))]
    {:name (symbol "logic" (str "forall-" arity "-truth"))
     :foreign/names [(get {1 "forall_true_iff"
                           2 "forall₂_true_iff"
                           3 "forall₃_true_iff"} arity)]
     :universes universes
     :type (forall outer (equivalence all-truth (truth)))
     :value
     (lam outer
          (conjoin
           (arrow all-truth (truth))
           (arrow (truth) all-truth)
           (lam [['all-evidence all-truth]] (trivial))
           (lam (vec (concat [['truth-evidence (truth)]] arguments))
                'truth-evidence)))}))

(def hand-theorem-specs
  [{:name 'logic/exists-proof-first
    :foreign/names ["Exists.fst"]
    :universes []
    :type
    (forall [['P 'Prop] ['Q (arrow 'P 'Prop)]
             ['evidence (proposition/existence [:zero] 'P 'Q)]]
            'P)
    :value
    (lam [['P 'Prop] ['Q (arrow 'P 'Prop)]
          ['evidence (proposition/existence [:zero] 'P 'Q)]]
         (use-witness
          [:zero] 'P 'Q 'P 'evidence
          (lam [['proof 'P] ['predicate-evidence (app 'Q 'proof)]]
               'proof)))}

   {:name 'logic/implication-equivalence
    :foreign/names ["Iff.imp"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
             ['left-domain (equivalence 'A 'C)]
             ['right-domain (equivalence 'B 'D)]]
            (equivalence (arrow 'A 'B) (arrow 'C 'D)))
    :value
    (lam [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
          ['left-domain (equivalence 'A 'C)]
          ['right-domain (equivalence 'B 'D)]]
         (conjoin
          (arrow (arrow 'A 'B) (arrow 'C 'D))
          (arrow (arrow 'C 'D) (arrow 'A 'B))
          (lam [['function (arrow 'A 'B)] ['value 'C]]
               (app (iff-forward 'B 'D 'right-domain)
                    (app 'function
                         (app (iff-backward 'A 'C 'left-domain)
                              'value))))
          (lam [['function (arrow 'C 'D)] ['value 'A]]
               (app (iff-backward 'B 'D 'right-domain)
                    (app 'function
                         (app (iff-forward 'A 'C 'left-domain)
                              'value))))))}

   {:name 'logic/forall-2-conjunction
    :foreign/names ["forall₂_and"]
    :universes ['u]
    :type
    (let [arguments [['x 'A] ['index (app 'I 'x)]]
          left (quantifier/nested-forall
                arguments (app 'P 'x 'index))
          right (quantifier/nested-forall
                 arguments (app 'Q 'x 'index))]
      (forall [['A sort-u]
               ['I (arrow 'A 'Prop)]
               ['P (quantifier/nested-forall arguments 'Prop)]
               ['Q (quantifier/nested-forall arguments 'Prop)]]
              (equivalence
               (quantifier/nested-forall
                arguments
                (conjunction (app 'P 'x 'index)
                             (app 'Q 'x 'index)))
               (conjunction left right))))
    :value
    (let [arguments [['x 'A] ['index (app 'I 'x)]]
          left (quantifier/nested-forall
                arguments (app 'P 'x 'index))
          right (quantifier/nested-forall
                 arguments (app 'Q 'x 'index))
          both (quantifier/nested-forall
                arguments
                (conjunction (app 'P 'x 'index)
                             (app 'Q 'x 'index)))]
      (lam [['A sort-u]
            ['I (arrow 'A 'Prop)]
            ['P (quantifier/nested-forall arguments 'Prop)]
            ['Q (quantifier/nested-forall arguments 'Prop)]]
           (conjoin
            (arrow both (conjunction left right))
            (arrow (conjunction left right) both)
            (lam [['all-both both]]
                 (conjoin
                  left right
                  (lam arguments
                       (conjunction-left
                        (app 'P 'x 'index) (app 'Q 'x 'index)
                        (app 'all-both 'x 'index)))
                  (lam arguments
                       (conjunction-right
                        (app 'P 'x 'index) (app 'Q 'x 'index)
                        (app 'all-both 'x 'index)))))
            (lam [['separate (conjunction left right)]]
                 (lam arguments
                      (conjoin
                       (app 'P 'x 'index) (app 'Q 'x 'index)
                       (app (conjunction-left left right 'separate)
                            'x 'index)
                       (app (conjunction-right left right 'separate)
                            'x 'index)))))))}

   {:name 'logic/or-eliminate-3
    :foreign/names ["Or.elim3"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
             ['either (disjunction 'A (disjunction 'B 'C))]
             ['on-a (arrow 'A 'D)]
             ['on-b (arrow 'B 'D)]
             ['on-c (arrow 'C 'D)]]
            'D)
    :value
    (lam [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
          ['either (disjunction 'A (disjunction 'B 'C))]
          ['on-a (arrow 'A 'D)]
          ['on-b (arrow 'B 'D)]
          ['on-c (arrow 'C 'D)]]
         (use-disjunction
          'A (disjunction 'B 'C) 'D 'either 'on-a
          (lam [['nested (disjunction 'B 'C)]]
               (use-disjunction 'B 'C 'D 'nested 'on-b 'on-c))))}

   {:name 'logic/exists-swap
    :foreign/names ["exists_swap"]
    :universes ['u 'v]
    :type
    (let [left (proposition/existence
                U 'A (lam [['x 'A]]
                          (proposition/existence
                           V 'B (lam [['y 'B]] (app 'P 'x 'y)))))
          right (proposition/existence
                 V 'B (lam [['y 'B]]
                           (proposition/existence
                            U 'A (lam [['x 'A]] (app 'P 'x 'y)))))]
      (forall [['A sort-u] ['B sort-v]
               ['P (arrow 'A 'B 'Prop)]]
              (equivalence left right)))
    :value
    (let [left (proposition/existence
                U 'A (lam [['x 'A]]
                          (proposition/existence
                           V 'B (lam [['y 'B]] (app 'P 'x 'y)))))
          right (proposition/existence
                 V 'B (lam [['y 'B]]
                           (proposition/existence
                            U 'A (lam [['x 'A]] (app 'P 'x 'y)))))]
      (lam [['A sort-u] ['B sort-v]
            ['P (arrow 'A 'B 'Prop)]]
           (conjoin
            (arrow left right) (arrow right left)
            (lam [['evidence left]]
                 (use-witness
                  U 'A
                  (lam [['x 'A]]
                       (proposition/existence
                        V 'B (lam [['y 'B]] (app 'P 'x 'y))))
                  right 'evidence
                  (lam [['x 'A]
                        ['inner
                         (proposition/existence
                          V 'B (lam [['y 'B]] (app 'P 'x 'y)))]]
                       (use-witness
                        V 'B (lam [['y 'B]] (app 'P 'x 'y))
                        right 'inner
                        (lam [['y 'B] ['proof (app 'P 'x 'y)]]
                             (witness
                              V 'B
                              (lam [['y 'B]]
                                   (proposition/existence
                                    U 'A
                                    (lam [['x 'A]] (app 'P 'x 'y))))
                              'y
                              (witness
                               U 'A (lam [['x 'A]] (app 'P 'x 'y))
                               'x 'proof)))))))
            (lam [['evidence right]]
                 (use-witness
                  V 'B
                  (lam [['y 'B]]
                       (proposition/existence
                        U 'A (lam [['x 'A]] (app 'P 'x 'y))))
                  left 'evidence
                  (lam [['y 'B]
                        ['inner
                         (proposition/existence
                          U 'A (lam [['x 'A]] (app 'P 'x 'y)))]]
                       (use-witness
                        U 'A (lam [['x 'A]] (app 'P 'x 'y))
                        left 'inner
                        (lam [['x 'A] ['proof (app 'P 'x 'y)]]
                             (witness
                              U 'A
                              (lam [['x 'A]]
                                   (proposition/existence
                                    V 'B
                                    (lam [['y 'B]] (app 'P 'x 'y))))
                              'x
                              (witness
                               V 'B (lam [['y 'B]] (app 'P 'x 'y))
                               'y 'proof))))))))))}

   {:name 'logic/exists-over-proof-equivalence
    :foreign/names ["exists_iff_of_forall"]
    :universes []
    :type
    (forall [['P 'Prop] ['Q (arrow 'P 'Prop)]
             ['all (forall [['proof 'P]] (app 'Q 'proof))]]
            (equivalence
             (proposition/existence [:zero] 'P 'Q) 'P))
    :value
    (let [some (proposition/existence [:zero] 'P 'Q)]
      (lam [['P 'Prop] ['Q (arrow 'P 'Prop)]
            ['all (forall [['proof 'P]] (app 'Q 'proof))]]
           (conjoin
            (arrow some 'P) (arrow 'P some)
            (lam [['evidence some]]
                 (use-witness
                  [:zero] 'P 'Q 'P 'evidence
                  (lam [['proof 'P] ['q-proof (app 'Q 'proof)]]
                       'proof)))
            (lam [['proof 'P]]
                 (witness [:zero] 'P 'Q 'proof
                          (app 'all 'proof))))))}

   {:name 'logic/implication-forall-proof-equivalence
    :foreign/names ["imp_forall_iff_forall"]
    :universes []
    :type
    (forall [['P 'Prop] ['Q (arrow 'P 'Prop)]]
            (equivalence
             (arrow 'P (forall [['proof 'P]] (app 'Q 'proof)))
             (forall [['proof 'P]] (app 'Q 'proof))))
    :value
    (let [all (forall [['proof 'P]] (app 'Q 'proof))]
      (lam [['P 'Prop] ['Q (arrow 'P 'Prop)]]
           (conjoin
            (arrow (arrow 'P all) all)
            (arrow all (arrow 'P all))
            (lam [['function (arrow 'P all)] ['proof 'P]]
                 (app 'function 'proof 'proof))
            (lam [['all-evidence all] ['ignored 'P]]
                 'all-evidence))))}

   {:name 'logic/forall-swap
    :foreign/names ["forall_swap"]
    :universes ['u 'v]
    :type
    (let [left (forall [['x 'A] ['y 'B]] (app 'P 'x 'y))
          right (forall [['y 'B] ['x 'A]] (app 'P 'x 'y))]
      (forall [['A sort-u] ['B sort-v]
               ['P (arrow 'A 'B 'Prop)]]
              (equivalence left right)))
    :value
    (let [left (forall [['x 'A] ['y 'B]] (app 'P 'x 'y))
          right (forall [['y 'B] ['x 'A]] (app 'P 'x 'y))]
      (lam [['A sort-u] ['B sort-v]
            ['P (arrow 'A 'B 'Prop)]]
           (conjoin
            (arrow left right) (arrow right left)
            (lam [['evidence left] ['y 'B] ['x 'A]]
                 (app 'evidence 'x 'y))
            (lam [['evidence right] ['x 'A] ['y 'B]]
                 (app 'evidence 'y 'x)))))}

   {:name 'logic/implication-forall-equivalence
    :foreign/names ["imp_forall_iff"]
    :universes ['u]
    :type
    (let [all (forall [['x 'A]] (app 'Q 'x))]
      (forall [['A sort-u] ['P 'Prop]
               ['Q (arrow 'A 'Prop)]]
              (equivalence
               (arrow 'P all)
               (forall [['x 'A]] (arrow 'P (app 'Q 'x))))))
    :value
    (let [all (forall [['x 'A]] (app 'Q 'x))
          distributed (forall [['x 'A]] (arrow 'P (app 'Q 'x)))]
      (lam [['A sort-u] ['P 'Prop]
            ['Q (arrow 'A 'Prop)]]
           (conjoin
            (arrow (arrow 'P all) distributed)
            (arrow distributed (arrow 'P all))
            (lam [['function (arrow 'P all)] ['x 'A] ['proof 'P]]
                 (app 'function 'proof 'x))
            (lam [['function distributed] ['proof 'P] ['x 'A]]
                 (app 'function 'x 'proof)))))}

   {:name 'logic/and-rotate
    :foreign/names ["And.rotate"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop]
             ['evidence (conjunction 'A (conjunction 'B 'C))]]
            (conjunction 'B (conjunction 'C 'A)))
    :value
    (lam [['A 'Prop] ['B 'Prop] ['C 'Prop]
          ['evidence (conjunction 'A (conjunction 'B 'C))]]
         (let [nested (conjunction-left
                       'A (conjunction 'B 'C) 'evidence)]
           (conjoin
            'B (conjunction 'C 'A)
            (conjunction-left
             'B 'C
             (conjunction-right
              'A (conjunction 'B 'C) 'evidence))
            (conjoin
             'C 'A
             (conjunction-right
              'B 'C
              (conjunction-right
               'A (conjunction 'B 'C) 'evidence))
             nested))))}

   {:name 'logic/or-rotate
    :foreign/names ["Or.rotate"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop]
             ['evidence (disjunction 'A (disjunction 'B 'C))]]
            (disjunction 'B (disjunction 'C 'A)))
    :value
    (lam [['A 'Prop] ['B 'Prop] ['C 'Prop]
          ['evidence (disjunction 'A (disjunction 'B 'C))]]
         (use-disjunction
          'A (disjunction 'B 'C)
          (disjunction 'B (disjunction 'C 'A)) 'evidence
          (lam [['a 'A]]
               (right-disjunct
                'B (disjunction 'C 'A)
                (right-disjunct 'C 'A 'a)))
          (lam [['nested (disjunction 'B 'C)]]
               (use-disjunction
                'B 'C (disjunction 'B (disjunction 'C 'A)) 'nested
                (lam [['b 'B]]
                     (left-disjunct 'B (disjunction 'C 'A) 'b))
                (lam [['c 'C]]
                     (right-disjunct
                      'B (disjunction 'C 'A)
                      (left-disjunct 'C 'A 'c)))))))}

   {:name 'logic/or-map-3
    :foreign/names ["Or.imp3"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop]
             ['D 'Prop] ['E 'Prop] ['F 'Prop]
             ['a-to-c (arrow 'A 'C)]
             ['b-to-d (arrow 'B 'D)]
             ['e-to-f (arrow 'E 'F)]
             ['evidence (disjunction 'A (disjunction 'B 'E))]]
            (disjunction 'C (disjunction 'D 'F)))
    :value
    (lam [['A 'Prop] ['B 'Prop] ['C 'Prop]
          ['D 'Prop] ['E 'Prop] ['F 'Prop]
          ['a-to-c (arrow 'A 'C)]
          ['b-to-d (arrow 'B 'D)]
          ['e-to-f (arrow 'E 'F)]
          ['evidence (disjunction 'A (disjunction 'B 'E))]]
         (use-disjunction
          'A (disjunction 'B 'E)
          (disjunction 'C (disjunction 'D 'F)) 'evidence
          (lam [['a 'A]]
               (left-disjunct
                'C (disjunction 'D 'F) (app 'a-to-c 'a)))
          (lam [['nested (disjunction 'B 'E)]]
               (use-disjunction
                'B 'E (disjunction 'C (disjunction 'D 'F)) 'nested
                (lam [['b 'B]]
                     (right-disjunct
                      'C (disjunction 'D 'F)
                      (left-disjunct 'D 'F (app 'b-to-d 'b))))
                (lam [['e 'E]]
                     (right-disjunct
                      'C (disjunction 'D 'F)
                      (right-disjunct 'D 'F (app 'e-to-f 'e))))))))}

   {:name 'logic/iff-or
    :foreign/names ["Iff.or"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
             ['left (equivalence 'A 'B)]
             ['right (equivalence 'C 'D)]]
            (equivalence
             (disjunction 'A 'C) (disjunction 'B 'D)))
    :value
    (let [source (disjunction 'A 'C)
          target (disjunction 'B 'D)]
      (lam [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
            ['left (equivalence 'A 'B)]
            ['right (equivalence 'C 'D)]]
           (conjoin
            (arrow source target) (arrow target source)
            (lam [['evidence source]]
                 (use-disjunction
                  'A 'C target 'evidence
                  (lam [['a 'A]]
                       (left-disjunct
                        'B 'D (app (iff-forward 'A 'B 'left) 'a)))
                  (lam [['c 'C]]
                       (right-disjunct
                        'B 'D (app (iff-forward 'C 'D 'right) 'c)))))
            (lam [['evidence target]]
                 (use-disjunction
                  'B 'D source 'evidence
                  (lam [['b 'B]]
                       (left-disjunct
                        'A 'C (app (iff-backward 'A 'B 'left) 'b)))
                  (lam [['d 'D]]
                       (right-disjunct
                        'A 'C (app (iff-backward 'C 'D 'right) 'd))))))))}

   {:name 'logic/exists-pair
    :foreign/names ["exists_and_exists_comm"]
    :universes ['u 'v]
    :type
    (let [left-exists (proposition/existence U 'A 'P)
          right-exists (proposition/existence V 'B 'Q)
          paired
          (proposition/existence
           U 'A
           (lam [['x 'A]]
                (proposition/existence
                 V 'B
                 (lam [['y 'B]]
                      (conjunction (app 'P 'x) (app 'Q 'y))))))]
      (forall [['A sort-u] ['B sort-v]
               ['P (arrow 'A 'Prop)] ['Q (arrow 'B 'Prop)]]
              (equivalence
               (conjunction left-exists right-exists) paired)))
    :value
    (let [left-exists (proposition/existence U 'A 'P)
          right-exists (proposition/existence V 'B 'Q)
          separate (conjunction left-exists right-exists)
          paired
          (proposition/existence
           U 'A
           (lam [['x 'A]]
                (proposition/existence
                 V 'B
                 (lam [['y 'B]]
                      (conjunction (app 'P 'x) (app 'Q 'y))))))]
      (lam [['A sort-u] ['B sort-v]
            ['P (arrow 'A 'Prop)] ['Q (arrow 'B 'Prop)]]
           (conjoin
            (arrow separate paired) (arrow paired separate)
            (lam [['evidence separate]]
                 (use-witness
                  U 'A 'P paired
                  (conjunction-left left-exists right-exists 'evidence)
                  (lam [['x 'A] ['px (app 'P 'x)]]
                       (use-witness
                        V 'B 'Q paired
                        (conjunction-right left-exists right-exists 'evidence)
                        (lam [['y 'B] ['qy (app 'Q 'y)]]
                             (witness
                              U 'A
                              (lam [['x 'A]]
                                   (proposition/existence
                                    V 'B
                                    (lam [['y 'B]]
                                         (conjunction
                                          (app 'P 'x) (app 'Q 'y)))))
                              'x
                              (witness
                               V 'B
                               (lam [['y 'B]]
                                    (conjunction (app 'P 'x) (app 'Q 'y)))
                               'y
                               (conjoin (app 'P 'x) (app 'Q 'y)
                                        'px 'qy))))))))
            (lam [['evidence paired]]
                 (use-witness
                  U 'A
                  (lam [['x 'A]]
                       (proposition/existence
                        V 'B
                        (lam [['y 'B]]
                             (conjunction (app 'P 'x) (app 'Q 'y)))))
                  separate 'evidence
                  (lam [['x 'A]
                        ['inner
                         (proposition/existence
                          V 'B
                          (lam [['y 'B]]
                               (conjunction
                                (app 'P 'x) (app 'Q 'y))))]]
                       (use-witness
                        V 'B
                        (lam [['y 'B]]
                             (conjunction (app 'P 'x) (app 'Q 'y)))
                        separate 'inner
                        (lam [['y 'B]
                              ['both
                               (conjunction (app 'P 'x) (app 'Q 'y))]]
                             (conjoin
                              left-exists right-exists
                              (witness
                               U 'A 'P 'x
                               (conjunction-left
                                (app 'P 'x) (app 'Q 'y) 'both))
                              (witness
                               V 'B 'Q 'y
                               (conjunction-right
                                (app 'P 'x) (app 'Q 'y) 'both)))))))))))}

   {:name 'logic/implication-swap
    :foreign/names ["Imp.swap"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['P 'Prop]]
            (equivalence
             (arrow 'A 'B 'P) (arrow 'B 'A 'P)))
    :value
    (lam [['A sort-u] ['B sort-v] ['P 'Prop]]
         (conjoin
          (arrow (arrow 'A 'B 'P) (arrow 'B 'A 'P))
          (arrow (arrow 'B 'A 'P) (arrow 'A 'B 'P))
          (lam [['function (arrow 'A 'B 'P)] ['b 'B] ['a 'A]]
               (app 'function 'a 'b))
          (lam [['function (arrow 'B 'A 'P)] ['a 'A] ['b 'B]]
               (app 'function 'b 'a))))}

   {:name 'logic/iff-and
    :foreign/names ["Iff.and"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
             ['left (equivalence 'A 'B)]
             ['right (equivalence 'C 'D)]]
            (equivalence
             (conjunction 'A 'C) (conjunction 'B 'D)))
    :value
    (let [source (conjunction 'A 'C)
          target (conjunction 'B 'D)]
      (lam [['A 'Prop] ['B 'Prop] ['C 'Prop] ['D 'Prop]
            ['left (equivalence 'A 'B)]
            ['right (equivalence 'C 'D)]]
           (conjoin
            (arrow source target) (arrow target source)
            (lam [['evidence source]]
                 (conjoin
                  'B 'D
                  (app (iff-forward 'A 'B 'left)
                       (conjunction-left 'A 'C 'evidence))
                  (app (iff-forward 'C 'D 'right)
                       (conjunction-right 'A 'C 'evidence))))
            (lam [['evidence target]]
                 (conjoin
                  'A 'C
                  (app (iff-backward 'A 'B 'left)
                       (conjunction-left 'B 'D 'evidence))
                  (app (iff-backward 'C 'D 'right)
                       (conjunction-right 'B 'D 'evidence)))))))}

   {:name 'logic/modus-tollens
    :foreign/names ["Function.mt"]
    :universes []
    :type
    (forall [['A 'Prop] ['B 'Prop]
             ['function (arrow 'A 'B)]
             ['not-b (negation 'B)]]
            (negation 'A))
    :value
    (lam [['A 'Prop] ['B 'Prop]
          ['function (arrow 'A 'B)]
          ['not-b (negation 'B)]
          ['a 'A]]
         (app 'not-b (app 'function 'a)))}])

(def theorem-specs
  (vec (concat [(nested-implication-spec 3)]
               hand-theorem-specs
               [(nested-implication-spec 2)]
               (map forall-truth-spec (range 1 4)))))

(def deferred-specs
  [{:foreign/name "Function.mtr" :reason :requires-classical-reasoning}
   {:foreign/name "imp_or" :reason :requires-classical-reasoning}
   {:foreign/name "imp_or'" :reason :requires-classical-reasoning}
   {:foreign/name "not_or_of_imp" :reason :requires-classical-reasoning}
   {:foreign/name "And.exists" :reason :requires-proof-irrelevance}
   {:foreign/name "forall_and_index" :reason :requires-proof-irrelevance}
   {:foreign/name "forall_and_index'" :reason :requires-proof-irrelevance}
   {:foreign/name "forall_true_left" :reason :requires-proof-irrelevance}
   {:foreign/name "Exists.snd" :reason :requires-proof-irrelevance}])

(def deferred-statements
  (mapv #(assoc % :statement-weakened? false :trusted-axiom-added? false)
        deferred-specs))

(def proved-foreign-names (set (mapcat :foreign/names theorem-specs)))
(def deferred-foreign-names (set (map :foreign/name deferred-statements)))
(def requested-foreign-names
  (into proved-foreign-names deferred-foreign-names))

(def nativeized-foreign-constants
  #{"And" "And.intro" "And.left" "And.right" "Exists" "Exists.fst"
    "Iff" "Not" "Or" "True" "True.intro"})

(defn- elaborate! [environment surface]
  (let [result (elaborate/core-expression environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Logic.Basic form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (let [prior (mathlib-unique-existence-transport/build)]
    (reduce
     (fn [{:keys [environment results] :as state} spec]
       (let [type (elaborate! environment (:type spec))
             value (elaborate! environment (:value spec))
             added
             (kernel/add-declaration
              environment
              {:rainbow/kind :theorem
               :rainbow/aliases #{(:name spec)}
               :rainbow/universes (:universes spec)
               :rainbow/type type :rainbow/value value
               :rainbow/transparency :opaque
               :rainbow/dependencies
               (into (term/constants type) (term/constants value))
               :rainbow/provenance
               {:origin :native :producer :logic-basic-proof-data
                :foreign/system :lean :foreign/library :mathlib
                :foreign/version mathlib/pinned-version
                :foreign/commit mathlib/pinned-commit
                :foreign/source source-path
                :foreign/names (:foreign/names spec)
                :foreign/proof-hidden? true}
               :rainbow/schema-version 1})]
         (when-not (= :accepted (:status added))
           (throw (ex-info "Logic.Basic proof rejected"
                           {:spec (:name spec) :result added})))
         (assoc state :environment (:environment added)
                :results (conj results
                               {:spec spec :declaration (:declaration added)}))))
     {:environment (:environment prior) :prior prior :results []}
     theorem-specs)))

(defn result-mappings [results]
  (mapv (fn [result]
          {:foreign/name (first (get-in result [:spec :foreign/names]))
           :native/id (get-in result [:declaration :rainbow/id])})
        results))

(defn all-mappings
  "Flattens the accumulated Mathlib proof lineage through Day 32."
  [{:keys [prior results]}]
  (vec (concat (mathlib-unique-existence-transport/all-mappings prior)
               (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        dependency-audit
        (mathlib/audit-statement-dependencies
         (:statements batch) nativeized-foreign-constants)
        {:keys [environment prior results]} (build)
        mappings (result-mappings results)
        all-mappings (all-mappings {:prior prior :results results})
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        axioms
        (into {}
              (map (fn [result]
                     [(get-in result [:spec :name])
                      (kernel/axioms
                       environment
                       (get-in result [:declaration :rainbow/id]))]))
              results)
        native-ids (mapv #(get-in % [:declaration :rainbow/id]) results)
        batch-names (set (map :foreign/name (:statements batch)))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names batch-names)
             (= 31 (count batch-names))
             (= 22 (count mappings) (count results)
                (count (distinct native-ids)))
             (= 67 (count proved-names) (:proved summary))
             (= 31 (:fully-nativeizable dependency-audit))
             (zero? (:with-unresolved dependency-audit))
             (every? empty? (vals axioms))
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :path source-path}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested (count batch-names)
          :proof-values :redacted}
         :selection
         {:foreign-theorems (vec (sort batch-names))
          :dependency-audit dependency-audit
          :independently-proved (count mappings)
          :deferred (count deferred-statements)
          :lean-proofs-visible-to-rainbow? false
          :nativeization :truth-falsity-disjunction-and-quantifier-proof-data
          :statement-weakened? false}
         :proofs {:foreign-statements-checked (count mappings)
                  :generated-families
                  {:nested-implication-arities [2 3]
                   :forall-truth-arities [1 2 3]}
                  :mappings mappings :axioms axioms}
         :deferred-statements deferred-statements
         :coverage {:independently-proved (:proved summary)
                    :theorem-declarations (:theorems summary)
                    :ratio (get-in summary [:coverage :ratio])
                    :percent (* 100 (get-in summary [:coverage :ratio]))
                    :all-mappings all-mappings}
         :capability-growth
         {:native-connectives
          ['proposition/truth 'proposition/falsity 'proposition/disjunction]
          :dependency-audit 'mathlib/audit-statement-dependencies
          :curriculum-correction
          :bounded-full-type-dependencies-before-proof-selection}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :mathlib-day32/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day32/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command second-path]]
  (if (= "replay" command)
    (let [result (load-report (or second-path report-path))]
      (println (pr-str result))
      (when-not (= :replayed (:status result)) (System/exit 1)))
    (let [value (report (or command default-catalog-path)
                        (or second-path default-statement-path))]
      (println (pr-str value))
      (when-not (= :passed (:status value)) (System/exit 1)))))
