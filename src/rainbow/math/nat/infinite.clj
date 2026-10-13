(ns rainbow.math.nat.infinite
  "Axiom-free Nat constructor discrimination, list bounds, and infinitude."
  (:require [rainbow.module :as module]
            [rainbow.algebra.finite :as finite-algebra]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def list-nat (finite-type/list-of type-level nat))

(defn- equality [left right]
  (function/app (function/const* 'equality/Eq [type-level])
                nat left right))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- succ [value]
  (function/app successor value))

(defn- membership [enumeration value]
  (function/app (function/const* 'list/membership [zero-level])
                nat enumeration value))

(defn- bound [enumeration]
  (function/app (function/const* 'list/nat-bound []) enumeration))

(defn- below [value upper]
  (function/app (function/const* 'nat/strict-below []) value upper))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(def predecessor-spec
  {:name 'nat/predecessor
   :kind :definition
   :universes []
   :type (function/arrow nat nat)
   :value
   (function/lam
    [['value nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nat)
     zero
     (function/lam [['previous nat] ['ignored nat]] 'previous)
     'value))})

(def strict-below-spec
  {:name 'nat/strict-below
   :kind :definition
   :universes []
   :type (function/arrow nat nat 'Prop)
   :value
   (function/lam
    [['value nat] ['upper nat]]
    (proposition/existence
     type-level nat
     (function/lam
      [['extra nat]]
      (equality (add (succ 'value) 'extra) 'upper))))})

(def nat-bound-spec
  {:name 'list/nat-bound
   :kind :definition
   :universes []
   :type (function/arrow list-nat nat)
   :value
   (function/lam
    [['enumeration list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] nat)
     zero
     (function/lam
      [['head nat] ['tail list-nat] ['tail-bound nat]]
      (add (succ 'head) 'tail-bound))
     'enumeration))})

(def definition-specs [predecessor-spec strict-below-spec nat-bound-spec])

(def zero-not-successor-spec
  (let [zero-equality (equality zero (succ 'value))
        discriminator
        (function/lam
         [['candidate nat]]
         (function/app
          (function/const* 'data/Nat.rec [type-level])
          (function/lam [['ignored nat]] 'Prop)
          (proposition/truth)
          (function/lam
           [['previous nat] ['ignored 'Prop]] (proposition/falsity))
          'candidate))]
    {:name 'nat/zero-not-successor
     :universes []
     :type
     (function/forall
      [['value nat]] (proposition/negation zero-equality))
     :value
     (function/lam
      [['value nat] ['same zero-equality]]
      (function/app 'same discriminator
                    (function/const* 'proposition/trivial [])))}))

(def successor-injective-spec
  (let [successor-equality (equality (succ 'left) (succ 'right))]
    {:name 'nat/successor-injective
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['same successor-equality]]
      (equality 'left 'right))
     :value
     (function/lam
      [['left nat] ['right nat] ['same successor-equality]]
      (function/app
       (function/const* 'equality/congruent-function
                        [type-level type-level])
       nat nat (function/const* 'nat/predecessor [])
       (succ 'left) (succ 'right) 'same))}))

(def add-associative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['middle nat] ['right nat]]
          (equality (add (add 'left 'middle) 'right)
                    (add 'left (add 'middle 'right)))))]
    {:name 'nat/add-associative
     :universes []
     :type
     (function/forall
      [['left nat] ['middle nat] ['right nat]]
      (equality (add (add 'left 'middle) 'right)
                (add 'left (add 'middle 'right))))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['middle nat] ['right nat]]
        (function/app (function/const* 'equality/reflexive [type-level])
                      nat (add 'middle 'right)))
       (function/lam
        [['previous nat] ['induction-hypothesis (function/app motive 'previous)]
         ['middle nat] ['right nat]]
        (function/app
         (function/const* 'equality/congruent-function
                          [type-level type-level])
         nat nat successor
         (add (add 'previous 'middle) 'right)
         (add 'previous (add 'middle 'right))
         (function/app 'induction-hypothesis 'middle 'right)))
       'left))}))

(def add-commutative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (equality (add 'left 'right) (add 'right 'left))))]
    {:name 'nat/add-commutative
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (equality (add 'left 'right) (add 'right 'left)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app
         (function/const* 'equality/symmetric [type-level])
         nat (add 'right zero) 'right
         (function/app
          (function/const* 'algebra/nat-add-zero-right []) 'right)))
       (function/lam
        [['previous nat] ['induction-hypothesis (function/app motive 'previous)]
         ['right nat]]
        (let [successor-congruence
              (function/app
               (function/const* 'equality/congruent-function
                                [type-level type-level])
               nat nat successor
               (add 'previous 'right) (add 'right 'previous)
               (function/app 'induction-hypothesis 'right))
              successor-right-symmetry
              (function/app
               (function/const* 'equality/symmetric [type-level])
               nat (add 'right (succ 'previous))
               (succ (add 'right 'previous))
               (function/app
                (function/const* 'algebra/nat-add-successor-right [])
                'right 'previous))]
          (function/app
           (function/const* 'equality/transitive [type-level])
           nat
           (succ (add 'previous 'right))
           (succ (add 'right 'previous))
           (add 'right (succ 'previous))
           successor-congruence successor-right-symmetry)))
       'left))}))

(def not-equal-successor-add-spec
  (let [claim
        (fn [value extra]
          (proposition/negation
           (equality value (succ (add value extra)))))
        motive
        (function/lam
         [['value nat]]
         (function/forall [['extra nat]] (claim 'value 'extra)))]
    {:name 'nat/not-equal-successor-add
     :universes []
     :type
     (function/forall
      [['value nat] ['extra nat]] (claim 'value 'extra))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['extra nat] ['same (equality zero (succ (add zero 'extra)))]]
        (function/app (function/const* 'nat/zero-not-successor [])
                      'extra 'same))
       (function/lam
        [['previous nat] ['induction-hypothesis (function/app motive 'previous)]
         ['extra nat]
         ['same (equality (succ 'previous)
                          (succ (add (succ 'previous) 'extra)))]]
        (function/app
         'induction-hypothesis 'extra
         (function/app
          (function/const* 'nat/successor-injective [])
          'previous (succ (add 'previous 'extra)) 'same)))
       'value))}))

(def member-below-bound-spec
  (let [motive
        (function/lam
         [['enumeration list-nat]]
         (function/forall
          [['value nat] ['member (membership 'enumeration 'value)]]
          (below 'value (bound 'enumeration))))
        nil-nat
        (function/app (function/const* 'data/nil [type-level]) nat)]
    {:name 'list/member-strictly-below-nat-bound
     :universes []
     :type
     (function/forall
      [['enumeration list-nat] ['value nat]
       ['member (membership 'enumeration 'value)]]
      (below 'value (bound 'enumeration)))
     :value
     (function/lam
      [['enumeration list-nat]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nat motive
       (function/lam
        [['value nat] ['member (membership nil-nat 'value)]]
        (function/app (function/const* 'proposition/explode [])
                      (below 'value (bound nil-nat)) 'member))
       (function/lam
        [['head nat] ['tail list-nat]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value nat]
         ['member
          (membership
           (function/app (function/const* 'data/cons [type-level])
                         nat 'head 'tail)
           'value)]]
        (let [head-case (equality 'value 'head)
              tail-case (membership 'tail 'value)
              target (below 'value (add (succ 'head) (bound 'tail)))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same-head head-case]]
            (witness
             type-level nat
             (function/lam
              [['extra nat]]
              (equality (add (succ 'value) 'extra)
                        (add (succ 'head) (bound 'tail))))
             (bound 'tail)
             (function/app
              (function/const* 'equality/congruent-function
                               [type-level type-level])
              nat nat
              (function/lam
               [['candidate nat]] (add (succ 'candidate) (bound 'tail)))
              'value 'head 'same-head)))
           (function/lam
            [['tail-member tail-case]]
            (function/app
             (function/const* 'proposition/use-witness [type-level])
             nat
             (function/lam
              [['extra nat]]
              (equality (add (succ 'value) 'extra) (bound 'tail)))
             target
             (function/app 'induction-hypothesis 'value 'tail-member)
             (function/lam
              [['extra nat]
               ['at-tail
                (equality (add (succ 'value) 'extra) (bound 'tail))]]
              (let [new-extra (add 'extra (succ 'head))
                    start (add (succ 'value) new-extra)
                    associated
                    (add (add (succ 'value) 'extra) (succ 'head))
                    swapped (add (bound 'tail) (succ 'head))
                    finish (add (succ 'head) (bound 'tail))
                    first-step
                    (function/app
                     (function/const* 'equality/symmetric [type-level])
                     nat associated start
                     (function/app
                      (function/const* 'nat/add-associative [])
                      (succ 'value) 'extra (succ 'head)))
                    second-step
                    (function/app
                     (function/const* 'equality/congruent-function
                                      [type-level type-level])
                     nat nat
                     (function/lam
                      [['candidate nat]] (add 'candidate (succ 'head)))
                     (add (succ 'value) 'extra) (bound 'tail) 'at-tail)
                    third-step
                    (function/app
                     (function/const* 'nat/add-commutative [])
                     (bound 'tail) (succ 'head))
                    first-two
                    (function/app
                     (function/const* 'equality/transitive [type-level])
                     nat start associated swapped first-step second-step)
                    complete
                    (function/app
                     (function/const* 'equality/transitive [type-level])
                     nat start swapped finish first-two third-step)]
                (witness
                 type-level nat
                 (function/lam
                  [['candidate nat]]
                  (equality (add (succ 'value) 'candidate) finish))
                 new-extra complete))))))))
       'enumeration))}))

(def infinite-nat-spec
  (let [finite-nat (finite-type/finite type-level nat)
        infinite-nat (finite-type/infinite type-level nat)
        cover
        (function/lam
         [['enumeration list-nat]]
         (function/forall
          [['value nat]]
          (finite-type/membership type-level nat 'enumeration 'value)))]
    {:name 'type/infinite-nat
     :universes []
     :type infinite-nat
     :value
     (function/lam
      [['finite-evidence finite-nat]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       list-nat cover (proposition/falsity) 'finite-evidence
       (function/lam
        [['enumeration list-nat]
         ['cover-evidence (function/app cover 'enumeration)]]
        (let [selected (bound 'enumeration)
              selected-member
              (function/app 'cover-evidence selected)]
          (function/app
           (function/const* 'proposition/use-witness [type-level])
           nat
           (function/lam
            [['extra nat]]
            (equality (add (succ selected) 'extra) selected))
           (proposition/falsity)
           (function/app
            (function/const* 'list/member-strictly-below-nat-bound [])
            'enumeration selected selected-member)
           (function/lam
            [['extra nat]
             ['too-large (equality (add (succ selected) 'extra) selected)]]
            (function/app
             (function/const* 'nat/not-equal-successor-add [])
             selected 'extra
             (function/app
              (function/const* 'equality/symmetric [type-level])
              nat (add (succ selected) 'extra) selected
              'too-large))))))))}))

(def theorem-specs
  [zero-not-successor-spec successor-injective-spec
   add-associative-spec add-commutative-spec not-equal-successor-add-spec
   member-below-bound-spec infinite-nat-spec])

(def arithmetic-theorem-names
  #{'algebra/nat-add-zero-right 'algebra/nat-add-successor-right})

(defn- extend-arithmetic [checked-environment]
  (let [with-add
        (finite-algebra/add-definition checked-environment
                                       (first finite-algebra/definition-specs))]
    (reduce
     (fn [current spec]
       (:environment (finite-algebra/register-theorem current spec)))
     with-add
     (filter #(contains? arithmetic-theorem-names (:name %))
             (finite-algebra/theorem-specs)))))

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat-infinitude expression failed elaboration"
                      {:expression expression :result result})))
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
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if (= :definition (:kind spec))
                                  :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :nat-finite-list-bound}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat-infinitude declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec (extend-arithmetic checked-environment) (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.infinite))
(defn arithmetic-ids [checked-environment]
  (into (sorted-map)
        (map (fn [name]
               [name (environment/resolve-id checked-environment name)]))
        (conj arithmetic-theorem-names 'algebra/nat-add)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
