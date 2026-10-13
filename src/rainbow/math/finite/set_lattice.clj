(ns rainbow.math.finite.set-lattice
  "Finite-set closure facts for complements, intersections, and suprema."
  (:refer-clojure :exclude [complement])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U finite-set/U)
(def data-level finite-set/data-level)
(def family-witness-level data-level)
(def type-u finite-set/type-u)

(defn complement [element source]
  (function/app (function/const* 'set/complement [U]) element source))

(defn intersection [element left right]
  (function/app (function/const* 'set/intersection [U])
                element left right))

(defn universal [element]
  (function/app (function/const* 'set/universal [U]) element))

(defn supremum [element family]
  (function/app (function/const* 'set/supremum [U]) element family))

(defn family-nonempty [element family]
  (let [set-a (finite-set/set-of element)]
    (function/app (function/const* 'set/nonempty [U])
                  set-a family)))

(defn family-of [element]
  (finite-set/set-of (finite-set/set-of element)))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(def finite-complement-universal-spec
  (let [set-a (finite-set/set-of 'A)
        list-a (finite-set/list-of 'A)
        all (universal 'A)
        outside (complement 'A all)
        all-nonempty (finite-set/nonempty 'A all)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        cover-predicate
        (function/lam
         [['enumeration list-a]]
         (finite-set/cover 'A outside 'enumeration))
        nil-cover
        (function/lam
         [['value 'A] ['outside-evidence (function/app outside 'value)]]
         (function/app 'outside-evidence
                       (function/const* 'proposition/trivial [])))]
    {:name 'set/finite-complement-universal
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['inhabited all-nonempty :explicit]]
      (finite-set/finite 'A outside))
     :value
     (function/lam
      [['A type-u :implicit] ['inhabited all-nonempty :explicit]]
      (witness data-level list-a cover-predicate nil-a nil-cover))}))

(def finite-complement-intersection-spec
  (let [set-a (finite-set/set-of 'A)
        outside-left (complement 'A 'left)
        outside-right (complement 'A 'right)
        overlap (intersection 'A 'left 'right)
        outside-both (complement 'A overlap)
        joined (finite-set/union 'A outside-left outside-right)
        left-nonempty (finite-set/nonempty 'A 'left)
        right-nonempty (finite-set/nonempty 'A 'right)
        overlap-nonempty (finite-set/nonempty 'A overlap)
        left-open
        (function/forall
         [['left-nonempty-evidence left-nonempty]]
         (finite-set/finite 'A outside-left))
        right-open
        (function/forall
         [['right-nonempty-evidence right-nonempty]]
         (finite-set/finite 'A outside-right))
        inclusion
        (function/lam
         [['value 'A]
          ['outside-both-evidence (function/app outside-both 'value)]]
         (let [left-member (function/app 'left 'value)
               right-member (function/app 'right 'value)
               not-left (proposition/negation left-member)
               not-right (proposition/negation right-member)]
           (function/app
            (function/const* 'logic/classical-cases [])
            left-member
            (function/app joined 'value)
            (function/lam
             [['left-evidence left-member]]
             (function/app
              (function/const* 'proposition/right-disjunct [])
              not-left not-right
              (function/lam
               [['right-evidence right-member]]
               (function/app
                'outside-both-evidence
                (function/app
                 (function/const* 'proposition/conjoin [])
                 left-member right-member
                 'left-evidence 'right-evidence)))))
            (function/lam
             [['not-left-evidence not-left]]
             (function/app
              (function/const* 'proposition/left-disjunct [])
              not-left not-right 'not-left-evidence)))))]
    {:name 'set/finite-complement-intersection
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left set-a :explicit] ['right set-a :explicit]
       ['left-open left-open :explicit]
       ['right-open right-open :explicit]
       ['overlap-nonempty-evidence overlap-nonempty :explicit]]
      (finite-set/finite 'A outside-both))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left set-a :explicit] ['right set-a :explicit]
       ['left-open left-open :explicit]
       ['right-open right-open :explicit]
       ['overlap-nonempty-evidence overlap-nonempty :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A overlap (finite-set/finite 'A outside-both)
       'overlap-nonempty-evidence
       (function/lam
        [['value 'A] ['overlap-member (function/app overlap 'value)]]
        (let [left-member
              (function/app
               (function/const* 'proposition/left [])
               (function/app 'left 'value) (function/app 'right 'value)
               'overlap-member)
              right-member
              (function/app
               (function/const* 'proposition/right [])
               (function/app 'left 'value) (function/app 'right 'value)
               'overlap-member)
              left-nonempty-evidence
              (witness data-level 'A 'left 'value left-member)
              right-nonempty-evidence
              (witness data-level 'A 'right 'value right-member)]
          (function/app
           (function/const* 'set/finite-subset-preserved [U])
           'A outside-both joined inclusion
           (function/app
            (function/const* 'set/finite-union-preserved [U])
            'A outside-left outside-right
            (function/app 'left-open left-nonempty-evidence)
            (function/app 'right-open right-nonempty-evidence)))))))}))

(def finite-complement-supremum-spec
  (let [set-a (finite-set/set-of 'A)
        family-type (family-of 'A)
        joined (supremum 'A 'family)
        outside-joined (complement 'A joined)
        member-open
        (function/forall
         [['source set-a]
          ['source-member (function/app 'family 'source)]
          ['source-nonempty-evidence
           (finite-set/nonempty 'A 'source)]]
         (finite-set/finite 'A (complement 'A 'source)))
        target
        (function/forall
         [['joined-nonempty-evidence (finite-set/nonempty 'A joined)]]
         (finite-set/finite 'A outside-joined))]
    {:name 'set/finite-complement-supremum
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['family family-type :explicit]
       ['member-open member-open :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['family family-type :explicit]
       ['member-open member-open :explicit]
       ['joined-nonempty-evidence
        (finite-set/nonempty 'A joined) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A joined (finite-set/finite 'A outside-joined)
       'joined-nonempty-evidence
       (function/lam
        [['value 'A] ['joined-member (function/app joined 'value)]]
        (let [source-predicate
              (function/lam
               [['source set-a]]
               (proposition/conjunction
                (function/app 'family 'source)
                (function/app 'source 'value)))]
          (function/app
           (function/const* 'proposition/use-witness
                            [family-witness-level])
           set-a source-predicate (finite-set/finite 'A outside-joined)
           'joined-member
           (function/lam
            [['source set-a]
             ['source-both
              (proposition/conjunction
               (function/app 'family 'source)
               (function/app 'source 'value))]]
            (let [source-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'family 'source)
                   (function/app 'source 'value) 'source-both)
                  source-value
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'family 'source)
                   (function/app 'source 'value) 'source-both)
                  outside-source (complement 'A 'source)
                  inclusion
                  (function/lam
                   [['candidate 'A]
                    ['outside-joined-evidence
                     (function/app outside-joined 'candidate)]]
                   (function/lam
                    [['source-candidate
                      (function/app 'source 'candidate)]]
                    (function/app
                     'outside-joined-evidence
                     (witness
                      family-witness-level set-a
                      (function/lam
                       [['candidate-source set-a]]
                       (proposition/conjunction
                        (function/app 'family 'candidate-source)
                        (function/app 'candidate-source 'candidate)))
                      'source
                      (function/app
                       (function/const* 'proposition/conjoin [])
                       (function/app 'family 'source)
                       (function/app 'source 'candidate)
                       source-member 'source-candidate)))))]
              (function/app
               (function/const* 'set/finite-subset-preserved [U])
               'A outside-joined outside-source inclusion
               (function/app
                'member-open 'source source-member
                (witness data-level 'A 'source 'value source-value))))))))))}))

(def infinite-intersection-of-finite-difference-spec
  (let [set-a (finite-set/set-of 'A)
        difference (finite-set/difference 'A 'left 'right)
        overlap (intersection 'A 'left 'right)
        partition (finite-set/union 'A difference overlap)
        inclusion
        (function/lam
         [['value 'A] ['left-member (function/app 'left 'value)]]
         (let [right-member (function/app 'right 'value)
               not-right (proposition/negation right-member)]
           (function/app
            (function/const* 'logic/classical-cases [])
            right-member (function/app partition 'value)
            (function/lam
             [['right-evidence right-member]]
             (function/app
              (function/const* 'proposition/right-disjunct [])
              (function/app difference 'value)
              (function/app overlap 'value)
              (function/app
               (function/const* 'proposition/conjoin [])
               (function/app 'left 'value) right-member
               'left-member 'right-evidence)))
            (function/lam
             [['not-right-evidence not-right]]
             (function/app
              (function/const* 'proposition/left-disjunct [])
              (function/app difference 'value)
              (function/app overlap 'value)
              (function/app
               (function/const* 'proposition/conjoin [])
               (function/app 'left 'value) not-right
               'left-member 'not-right-evidence))))))]
    {:name 'set/infinite-intersection-of-finite-difference
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left set-a :implicit] ['right set-a :implicit]
       ['left-infinite (finite-set/infinite 'A 'left) :explicit]
       ['difference-finite (finite-set/finite 'A difference) :explicit]]
      (finite-set/infinite 'A overlap))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left set-a :implicit] ['right set-a :implicit]
       ['left-infinite (finite-set/infinite 'A 'left) :explicit]
       ['difference-finite (finite-set/finite 'A difference) :explicit]
       ['overlap-finite (finite-set/finite 'A overlap)]]
      (function/app
       'left-infinite
       (function/app
        (function/const* 'set/finite-subset-preserved [U])
        'A 'left partition inclusion
        (function/app
         (function/const* 'set/finite-union-preserved [U])
         'A difference overlap
         'difference-finite 'overlap-finite))))}))

(def theorem-specs
  [finite-complement-universal-spec
   finite-complement-intersection-spec
   finite-complement-supremum-spec
   infinite-intersection-of-finite-difference-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-set lattice theorem failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-theorem [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-set-lattice-algebra}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-set lattice theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (doseq [required ['set/finite-union-preserved
                    'set/finite-subset-preserved
                    'logic/classical-cases]]
    (when-not (environment/resolve-id checked-environment required)
      (throw (ex-info "Finite-set lattice dependency is unavailable"
                      {:error/category :finite-set/lattice-dependency-missing
                       :required required}))))
  (reduce add-theorem checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
