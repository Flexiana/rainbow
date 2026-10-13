(ns rainbow.math.logic.proposition
  "Native proof-data encodings for core constructive propositions.

  Truth, falsity, conjunction, disjunction, existence, and unique existence
  are impredicative eliminators into Prop. Their introduction and elimination
  behavior stays explicit Clojure data and requires no new kernel rule or
  trusted primitive."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.equality :as equality]
            [rainbow.term :as term]))

(def U [:param 'u])
(def sort-u [:sort U])

(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn arrow [& values] (into [:->] values))
(defn app [function & arguments] (into [:app function] arguments))
(defn const* [alias levels] [:const alias (vec levels)])

(defn conjunction [left right]
  (app (const* 'proposition/conjunction []) left right))

(defn truth []
  (const* 'proposition/truth []))

(defn falsity []
  (const* 'proposition/falsity []))

(defn disjunction [left right]
  (app (const* 'proposition/disjunction []) left right))

(defn negation [value]
  (arrow value (falsity)))

(defn existence [level carrier predicate]
  (app (const* 'proposition/existence [level]) carrier predicate))

(defn equality [level carrier left right]
  (app (const* 'equality/Eq [level]) carrier left right))

(defn inequality [level carrier left right]
  (app (const* 'equality/inequality [level]) carrier left right))

(defn uniqueness [level carrier predicate value]
  (forall [['other carrier]
           ['other-evidence (app predicate 'other)]]
          (equality level carrier 'other value)))

(defn unique-existence [level carrier predicate]
  (app (const* 'proposition/unique-existence [level]) carrier predicate))

(defn equivalence [left right]
  (conjunction (arrow left right) (arrow right left)))

(defn introduce-equivalence [left right forward backward]
  (app (const* 'proposition/equivalence-intro [])
       left right forward backward))

(defn forward-equivalence [left right equivalent evidence]
  (app (const* 'proposition/equivalence-forward [])
       left right equivalent evidence))

(defn backward-equivalence [left right equivalent evidence]
  (app (const* 'proposition/equivalence-backward [])
       left right equivalent evidence))

(def connective-specs
  [{:name 'proposition/truth
    :kind :definition
    :universes []
    :transparency :reducible
    :type 'Prop
    :value
    (forall [['result 'Prop]
             ['evidence 'result]]
            'result)}

   {:name 'proposition/falsity
    :kind :definition
    :universes []
    :transparency :reducible
    :type 'Prop
    :value (forall [['result 'Prop]] 'result)}

   {:name 'proposition/conjunction
    :kind :definition
    :universes []
    :transparency :reducible
    :type (forall [['left 'Prop] ['right 'Prop]] 'Prop)
    :value
    (lam [['left 'Prop] ['right 'Prop]]
         (forall [['result 'Prop]
                  ['continue (arrow 'left 'right 'result)]]
                 'result))}

   {:name 'proposition/equivalence
    :kind :definition
    :universes []
    :transparency :reducible
    :type (forall [['left 'Prop] ['right 'Prop]] 'Prop)
    :value
    (lam [['left 'Prop] ['right 'Prop]]
         (conjunction (arrow 'left 'right)
                      (arrow 'right 'left)))}

   {:name 'proposition/negation
    :kind :definition
    :universes []
    :transparency :reducible
    :type (forall [['value 'Prop]] 'Prop)
    :value
    (lam [['value 'Prop]]
         (arrow 'value (falsity)))}

   {:name 'equality/inequality
    :kind :definition
    :universes ['u]
    :transparency :reducible
    :type (forall [['carrier sort-u]
                   ['left 'carrier] ['right 'carrier]]
                  'Prop)
    :value
    (lam [['carrier sort-u]
          ['left 'carrier] ['right 'carrier]]
         (negation (equality U 'carrier 'left 'right)))}

   {:name 'proposition/disjunction
    :kind :definition
    :universes []
    :transparency :reducible
    :type (forall [['left 'Prop] ['right 'Prop]] 'Prop)
    :value
    (lam [['left 'Prop] ['right 'Prop]]
         (forall [['result 'Prop]
                  ['on-left (arrow 'left 'result)]
                  ['on-right (arrow 'right 'result)]]
                 'result))}

   {:name 'proposition/existence
    :kind :definition
    :universes ['u]
    :transparency :reducible
    :type (forall [['carrier sort-u]
                   ['predicate (arrow 'carrier 'Prop)]]
                  'Prop)
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]]
         (forall [['result 'Prop]
                  ['continue
                   (forall [['value 'carrier]
                            ['evidence (app 'predicate 'value)]]
                           'result)]]
                 'result))}

   {:name 'proposition/unique-existence
    :kind :definition
    :universes ['u]
    :transparency :reducible
    :type (forall [['carrier sort-u]
                   ['predicate (arrow 'carrier 'Prop)]]
                  'Prop)
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]]
         (existence
          U 'carrier
          (lam [['value 'carrier]]
               (conjunction
                (app 'predicate 'value)
                (uniqueness U 'carrier 'predicate 'value)))))}])

(def theorem-specs
  [{:name 'proposition/trivial
    :universes []
    :type (truth)
    :value
    (lam [['result 'Prop]
          ['evidence 'result]]
         'evidence)}

   {:name 'proposition/explode
    :universes []
    :type (forall [['result 'Prop]
                   ['impossible (falsity)]]
                  'result)
    :value
    (lam [['result 'Prop]
          ['impossible (falsity)]]
         (app 'impossible 'result))}

   {:name 'proposition/conjoin
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['left-evidence 'left] ['right-evidence 'right]]
            (conjunction 'left 'right))
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['left-evidence 'left] ['right-evidence 'right]
          ['result 'Prop]
          ['continue (arrow 'left 'right 'result)]]
         (app 'continue 'left-evidence 'right-evidence))}

   {:name 'proposition/left
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['both (conjunction 'left 'right)]]
            'left)
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['both (conjunction 'left 'right)]]
         (app 'both 'left
              (lam [['left-evidence 'left] ['right-evidence 'right]]
                   'left-evidence)))}

   {:name 'proposition/right
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['both (conjunction 'left 'right)]]
            'right)
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['both (conjunction 'left 'right)]]
         (app 'both 'right
              (lam [['left-evidence 'left] ['right-evidence 'right]]
                   'right-evidence)))}

   {:name 'proposition/equivalence-intro
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['forward (arrow 'left 'right)]
             ['backward (arrow 'right 'left)]]
            (equivalence 'left 'right))
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['forward (arrow 'left 'right)]
          ['backward (arrow 'right 'left)]]
         (app (const* 'proposition/conjoin [])
              (arrow 'left 'right) (arrow 'right 'left)
              'forward 'backward))}

   {:name 'proposition/equivalence-forward
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['equivalent (equivalence 'left 'right)]
             ['evidence 'left]]
            'right)
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['equivalent (equivalence 'left 'right)]
          ['evidence 'left]]
         (app
          (app (const* 'proposition/left [])
               (arrow 'left 'right) (arrow 'right 'left) 'equivalent)
          'evidence))}

   {:name 'proposition/equivalence-backward
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['equivalent (equivalence 'left 'right)]
             ['evidence 'right]]
            'left)
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['equivalent (equivalence 'left 'right)]
          ['evidence 'right]]
         (app
          (app (const* 'proposition/right [])
               (arrow 'left 'right) (arrow 'right 'left) 'equivalent)
          'evidence))}

   {:name 'proposition/equivalence-congruence
    :universes []
    :type
    (forall [['left-source 'Prop :implicit] ['right-source 'Prop :implicit]
             ['left-target 'Prop :implicit] ['right-target 'Prop :implicit]
             ['sources-equivalent
              (equivalence 'left-source 'right-source)]
             ['targets-equivalent
              (equivalence 'left-target 'right-target)]]
            (equivalence
             (equivalence 'left-source 'left-target)
             (equivalence 'right-source 'right-target)))
    :value
    (lam
     [['left-source 'Prop :implicit] ['right-source 'Prop :implicit]
      ['left-target 'Prop :implicit] ['right-target 'Prop :implicit]
      ['sources-equivalent
       (equivalence 'left-source 'right-source)]
      ['targets-equivalent
       (equivalence 'left-target 'right-target)]]
     (introduce-equivalence
      (equivalence 'left-source 'left-target)
      (equivalence 'right-source 'right-target)
      (lam
       [['left-equivalent
         (equivalence 'left-source 'left-target)]]
       (introduce-equivalence
        'right-source 'right-target
        (lam [['right-source-evidence 'right-source]]
             (forward-equivalence
              'left-target 'right-target 'targets-equivalent
              (forward-equivalence
               'left-source 'left-target 'left-equivalent
               (backward-equivalence
                'left-source 'right-source 'sources-equivalent
                'right-source-evidence))))
        (lam [['right-target-evidence 'right-target]]
             (forward-equivalence
              'left-source 'right-source 'sources-equivalent
              (backward-equivalence
               'left-source 'left-target 'left-equivalent
               (backward-equivalence
                'left-target 'right-target 'targets-equivalent
                'right-target-evidence))))))
      (lam
       [['right-equivalent
         (equivalence 'right-source 'right-target)]]
       (introduce-equivalence
        'left-source 'left-target
        (lam [['left-source-evidence 'left-source]]
             (backward-equivalence
              'left-target 'right-target 'targets-equivalent
              (forward-equivalence
               'right-source 'right-target 'right-equivalent
               (forward-equivalence
                'left-source 'right-source 'sources-equivalent
                'left-source-evidence))))
        (lam [['left-target-evidence 'left-target]]
             (backward-equivalence
              'left-source 'right-source 'sources-equivalent
              (backward-equivalence
               'right-source 'right-target 'right-equivalent
               (forward-equivalence
                'left-target 'right-target 'targets-equivalent
                'left-target-evidence))))))))}

   {:name 'proposition/witness
    :universes ['u]
    :type
    (forall [['carrier sort-u]
             ['predicate (arrow 'carrier 'Prop)]
             ['value 'carrier]
             ['evidence (app 'predicate 'value)]]
            (existence U 'carrier 'predicate))
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]
          ['value 'carrier]
          ['evidence (app 'predicate 'value)]
          ['result 'Prop]
          ['continue
           (forall [['candidate 'carrier]
                    ['candidate-evidence (app 'predicate 'candidate)]]
                   'result)]]
         (app 'continue 'value 'evidence))}

   {:name 'proposition/use-witness
    :universes ['u]
    :type
    (forall [['carrier sort-u]
             ['predicate (arrow 'carrier 'Prop)]
             ['result 'Prop]
             ['some-evidence (existence U 'carrier 'predicate)]
             ['continue
              (forall [['value 'carrier]
                       ['evidence (app 'predicate 'value)]]
                      'result)]]
            'result)
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]
          ['result 'Prop]
          ['some-evidence (existence U 'carrier 'predicate)]
          ['continue
           (forall [['value 'carrier]
                    ['evidence (app 'predicate 'value)]]
                   'result)]]
         (app 'some-evidence 'result 'continue))}

   {:name 'proposition/left-disjunct
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['evidence 'left]]
            (disjunction 'left 'right))
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['evidence 'left]
          ['result 'Prop]
          ['on-left (arrow 'left 'result)]
          ['on-right (arrow 'right 'result)]]
         (app 'on-left 'evidence))}

   {:name 'proposition/right-disjunct
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop]
             ['evidence 'right]]
            (disjunction 'left 'right))
    :value
    (lam [['left 'Prop] ['right 'Prop]
          ['evidence 'right]
          ['result 'Prop]
          ['on-left (arrow 'left 'result)]
          ['on-right (arrow 'right 'result)]]
         (app 'on-right 'evidence))}

   {:name 'proposition/use-disjunction
    :universes []
    :type
    (forall [['left 'Prop] ['right 'Prop] ['result 'Prop]
             ['either (disjunction 'left 'right)]
             ['on-left (arrow 'left 'result)]
             ['on-right (arrow 'right 'result)]]
            'result)
    :value
    (lam [['left 'Prop] ['right 'Prop] ['result 'Prop]
          ['either (disjunction 'left 'right)]
          ['on-left (arrow 'left 'result)]
          ['on-right (arrow 'right 'result)]]
         (app 'either 'result 'on-left 'on-right))}

   {:name 'proposition/unique-witness
    :universes ['u]
    :type
    (forall [['carrier sort-u]
             ['predicate (arrow 'carrier 'Prop)]
             ['value 'carrier]
             ['evidence (app 'predicate 'value)]
             ['unique (uniqueness U 'carrier 'predicate 'value)]]
            (unique-existence U 'carrier 'predicate))
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]
          ['value 'carrier]
          ['evidence (app 'predicate 'value)]
          ['unique (uniqueness U 'carrier 'predicate 'value)]
          ['result 'Prop]
          ['continue
           (forall [['candidate 'carrier]
                    ['both
                     (conjunction
                      (app 'predicate 'candidate)
                      (uniqueness U 'carrier 'predicate 'candidate))]]
                   'result)]]
         (app 'continue 'value
              (app (const* 'proposition/conjoin [])
                   (app 'predicate 'value)
                   (uniqueness U 'carrier 'predicate 'value)
                   'evidence 'unique)))}

   {:name 'proposition/use-unique-witness
    :universes ['u]
    :type
    (forall [['carrier sort-u]
             ['predicate (arrow 'carrier 'Prop)]
             ['result 'Prop]
             ['some-evidence (unique-existence U 'carrier 'predicate)]
             ['continue
              (forall [['value 'carrier]
                       ['evidence (app 'predicate 'value)]
                       ['unique (uniqueness U 'carrier 'predicate 'value)]]
                      'result)]]
            'result)
    :value
    (lam [['carrier sort-u]
          ['predicate (arrow 'carrier 'Prop)]
          ['result 'Prop]
          ['some-evidence (unique-existence U 'carrier 'predicate)]
          ['continue
           (forall [['value 'carrier]
                    ['evidence (app 'predicate 'value)]
                    ['unique (uniqueness U 'carrier 'predicate 'value)]]
                   'result)]]
         (app
          'some-evidence 'result
          (lam [['value 'carrier]
                ['both
                 (conjunction
                  (app 'predicate 'value)
                  (uniqueness U 'carrier 'predicate 'value))]]
               (app
                'both 'result
                (lam [['evidence (app 'predicate 'value)]
                      ['unique (uniqueness U 'carrier 'predicate 'value)]]
                     (app 'continue 'value 'evidence 'unique))))))}])

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Proposition form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (or (:kind spec) :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type) (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :proposition-proof-data}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Proposition declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn build-environment []
  (reduce add-spec
          (equality/build-environment)
          (into connective-specs theorem-specs)))

(defn report []
  (let [checked-environment (build-environment)
        names (mapv :name (concat connective-specs theorem-specs))]
    {:status :passed
     :connectives (mapv :name connective-specs)
     :theorems (mapv :name theorem-specs)
     :axioms (into {} (map (fn [name]
                            [name (kernel/axioms checked-environment name)]))
                   names)
     :trusted-base-change :none}))

(defn -main [& _]
  (println (pr-str (report))))
