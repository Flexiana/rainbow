(ns rainbow.math.logic.infinite-injection
  "Classical, sort-polymorphic infinitude transport along injections."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def L [:param 'l])
(def M [:param 'm])
(def sort-l [:sort L])
(def sort-m [:sort M])

(defn- list-of [level carrier]
  (finite-type/list-of level carrier))

(defn- membership [level carrier enumeration value]
  (finite-type/membership level carrier enumeration value))

(defn- finite [level carrier]
  (finite-type/finite level carrier))

(defn- infinite [level carrier]
  (finite-type/infinite level carrier))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(def preimage-representatives-spec
  (let [list-source (list-of L 'Source)
        list-target (list-of M 'Target)
        nil-source
        (function/app (function/const* 'data/nil [L]) 'Source)
        nil-target
        (function/app (function/const* 'data/nil [M]) 'Target)
        injection
        (function/injective L M 'Source 'Target 'mapping)
        representative-cover
        (fn [target-enumeration source-enumeration]
          (function/forall
           [['value 'Source]
            ['image-member
             (membership M 'Target target-enumeration
                         (function/app 'mapping 'value))]]
           (membership L 'Source source-enumeration 'value)))
        result
        (fn [target-enumeration]
          (proposition/existence
           L list-source
           (function/lam
            [['source-enumeration list-source]]
            (representative-cover target-enumeration
                                  'source-enumeration))))
        motive
        (function/lam
         [['target-enumeration list-target]]
         (result 'target-enumeration))]
    {:name 'list/preimage-representatives
     :universes ['l 'm]
     :type
     (function/forall
      [['Source sort-l] ['Target sort-m]
       ['mapping (function/arrow 'Source 'Target)]
       ['injective injection]
       ['target-enumeration list-target]]
      (result 'target-enumeration))
     :value
     (function/lam
      [['Source sort-l] ['Target sort-m]
       ['mapping (function/arrow 'Source 'Target)]
       ['injective injection]
       ['target-enumeration list-target]]
      (function/app
       (function/const* 'data/List.rec [M zero-level])
       'Target motive
       (witness
        L list-source
        (function/lam
         [['source-enumeration list-source]]
         (representative-cover nil-target 'source-enumeration))
        nil-source
        (function/lam
         [['value 'Source]
          ['impossible
           (membership M 'Target nil-target
                       (function/app 'mapping 'value))]]
         (function/app
          (function/const* 'proposition/explode [])
          (membership L 'Source nil-source 'value)
          'impossible)))
       (function/lam
        [['head 'Target] ['tail list-target]
         ['induction-hypothesis (result 'tail)]]
        (let [target-enumeration
              (function/app (function/const* 'data/cons [M])
                            'Target 'head 'tail)
              target-result (result target-enumeration)
              representative-predicate
              (function/lam
               [['candidate 'Source]]
               (equality M 'Target
                         (function/app 'mapping 'candidate) 'head))
              representative-exists
              (proposition/existence L 'Source representative-predicate)]
          (function/app
           (function/const* 'proposition/use-witness [L])
           list-source
           (function/lam
            [['source-enumeration list-source]]
            (representative-cover 'tail 'source-enumeration))
           target-result 'induction-hypothesis
           (function/lam
            [['tail-representatives list-source]
             ['tail-cover
              (representative-cover 'tail 'tail-representatives)]]
            (function/app
             (function/const* 'logic/classical-cases [])
             representative-exists target-result
             (function/lam
              [['some-representative representative-exists]]
              (function/app
               (function/const* 'proposition/use-witness [L])
               'Source representative-predicate target-result
               'some-representative
               (function/lam
                [['representative 'Source]
                 ['representative-image
                  (equality M 'Target
                            (function/app 'mapping 'representative) 'head)]]
                (let [source-enumeration
                      (function/app (function/const* 'data/cons [L])
                                    'Source 'representative
                                    'tail-representatives)]
                  (witness
                   L list-source
                   (function/lam
                    [['candidate-enumeration list-source]]
                    (representative-cover target-enumeration
                                          'candidate-enumeration))
                   source-enumeration
                   (function/lam
                    [['value 'Source]
                     ['image-member
                      (membership M 'Target target-enumeration
                                  (function/app 'mapping 'value))]]
                    (let [at-head
                          (equality M 'Target
                                    (function/app 'mapping 'value) 'head)
                          in-tail
                          (membership M 'Target 'tail
                                      (function/app 'mapping 'value))
                          same-value
                          (equality L 'Source 'value 'representative)
                          tail-member
                          (membership L 'Source 'tail-representatives 'value)]
                      (function/app
                       (function/const* 'proposition/use-disjunction [])
                       at-head in-tail
                       (proposition/disjunction same-value tail-member)
                       'image-member
                       (function/lam
                        [['value-image at-head]]
                        (function/app
                         (function/const* 'proposition/left-disjunct [])
                         same-value tail-member
                         (function/app
                          'injective 'value 'representative
                          (function/app
                           (function/const* 'equality/transitive [M])
                           'Target
                           (function/app 'mapping 'value) 'head
                           (function/app 'mapping 'representative)
                           'value-image
                           (function/app
                            (function/const* 'equality/symmetric [M])
                            'Target
                            (function/app 'mapping 'representative) 'head
                            'representative-image)))))
                       (function/lam
                        [['tail-image in-tail]]
                        (function/app
                         (function/const* 'proposition/right-disjunct [])
                         same-value tail-member
                         (function/app 'tail-cover 'value
                                       'tail-image)))))))))))
             (function/lam
              [['no-representative
                (proposition/negation representative-exists)]]
              (witness
               L list-source
               (function/lam
                [['candidate-enumeration list-source]]
                (representative-cover target-enumeration
                                      'candidate-enumeration))
               'tail-representatives
               (function/lam
                [['value 'Source]
                 ['image-member
                  (membership M 'Target target-enumeration
                              (function/app 'mapping 'value))]]
                (let [at-head
                      (equality M 'Target
                                (function/app 'mapping 'value) 'head)
                      in-tail
                      (membership M 'Target 'tail
                                  (function/app 'mapping 'value))
                      target-member
                      (membership L 'Source 'tail-representatives 'value)]
                  (function/app
                   (function/const* 'proposition/use-disjunction [])
                   at-head in-tail target-member 'image-member
                   (function/lam
                    [['value-image at-head]]
                    (function/app
                     (function/const* 'proposition/explode []) target-member
                     (function/app
                      'no-representative
                      (witness L 'Source representative-predicate
                               'value 'value-image))))
                   (function/lam
                    [['tail-image in-tail]]
                    (function/app 'tail-cover 'value 'tail-image))))))))))))
       'target-enumeration))}))

(def finite-of-injection-spec
  (let [list-source (list-of L 'Source)
        list-target (list-of M 'Target)
        source-cover
        (function/lam
         [['enumeration list-source]]
         (function/forall
          [['value 'Source]]
          (membership L 'Source 'enumeration 'value)))
        target-cover
        (function/lam
         [['enumeration list-target]]
         (function/forall
          [['value 'Target]]
          (membership M 'Target 'enumeration 'value)))
        injection
        (function/injective L M 'Source 'Target 'mapping)]
    {:name 'type/finite-of-injection
     :universes ['l 'm]
     :type
     (function/forall
      [['Source sort-l :implicit] ['Target sort-m :implicit]
       ['mapping (function/arrow 'Source 'Target) :explicit]
       ['injective injection :explicit]
       ['target-finite (finite M 'Target) :explicit]]
      (finite L 'Source))
     :value
     (function/lam
      [['Source sort-l :implicit] ['Target sort-m :implicit]
       ['mapping (function/arrow 'Source 'Target) :explicit]
       ['injective injection :explicit]
       ['target-finite (finite M 'Target) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [M])
       list-target target-cover (finite L 'Source) 'target-finite
       (function/lam
        [['target-enumeration list-target]
         ['covers-target (function/app target-cover 'target-enumeration)]]
        (let [representative-cover
              (function/lam
               [['source-enumeration list-source]]
               (function/forall
                [['value 'Source]
                 ['image-member
                  (membership M 'Target 'target-enumeration
                              (function/app 'mapping 'value))]]
                (membership L 'Source 'source-enumeration 'value)))]
          (function/app
           (function/const* 'proposition/use-witness [L])
           list-source representative-cover (finite L 'Source)
           (function/app
            (function/const* 'list/preimage-representatives [L M])
            'Source 'Target 'mapping 'injective 'target-enumeration)
           (function/lam
            [['source-enumeration list-source]
             ['covers-images
              (function/app representative-cover 'source-enumeration)]]
            (witness
             L list-source source-cover 'source-enumeration
             (function/lam
              [['value 'Source]]
              (function/app
               'covers-images 'value
               (function/app 'covers-target
                             (function/app 'mapping 'value)))))))))))}))

(def infinite-of-injection-spec
  (let [source-infinite (infinite M 'B)
        target-infinite (infinite L 'A)
        injection (function/injective M L 'B 'A 'mapping)]
    {:name 'type/infinite-of-injection
     :universes ['l 'm]
     :type
     (function/forall
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['source-infinite source-infinite :implicit]
       ['mapping (function/arrow 'B 'A) :explicit]
       ['injective injection :explicit]]
      target-infinite)
     :value
     (function/lam
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['source-infinite source-infinite :implicit]
       ['mapping (function/arrow 'B 'A) :explicit]
       ['injective injection :explicit]
       ['target-finite (finite L 'A)]]
      (function/app
       'source-infinite
       (function/app
        (function/const* 'type/finite-of-injection [M L])
        'B 'A 'mapping 'injective 'target-finite)))}))

(def theorem-specs
  [preimage-representatives-spec finite-of-injection-spec
   infinite-of-injection-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Infinite-injection expression failed elaboration"
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
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :sort-polymorphic-infinite-injection}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Infinite-injection declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-theorem checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.logic.infinite-injection))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
