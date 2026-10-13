(ns rainbow.math.sets.finset.range
  "Native initial segments of Nat and finite-Finset range bounds."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def proposition-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def type-u [:sort [:succ U]])
(def type-v [:sort [:succ V]])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def list-nat
  (function/app (function/const* 'data/List [type-level]) nat))
(def set-nat
  (function/app (function/const* 'set/Set [zero-level]) nat))
(def finset-nat
  (function/app (function/const* 'finset/Finset [zero-level]) nat))

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- equality [carrier left right]
  (function/app (function/const* 'equality/Eq [type-level])
                carrier left right))

(defn- nat-equality [left right]
  (equality nat left right))

(defn- membership [enumeration value]
  (function/app (function/const* 'list/membership [zero-level])
                nat enumeration value))

(defn- range-list [upper]
  (function/app (function/const* 'list/nat-range []) upper))

(defn- below [value upper]
  (function/app (function/const* 'nat/strict-below []) value upper))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- range-finset [upper]
  (function/app (function/const* 'finset/range []) upper))

(defn- to-set [source]
  (function/app (function/const* 'finset/to-set [zero-level]) nat source))

(defn- finite-evidence [source]
  (function/app (function/const* 'finset/finite-evidence [zero-level])
                nat source))

(defn- subset [left right]
  (function/app (function/const* 'finset/subset [zero-level])
                nat left right))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- proposition-congruence [carrier mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [type-level proposition-level])
   carrier 'Prop mapping left right same))

(defn- proposition-forward [left right same evidence]
  (function/app (function/const* 'equality/proposition-forward [])
                left right same evidence))

(def nat-range-spec
  {:name 'list/nat-range
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat list-nat)
   :value
   (function/lam
    [['upper nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] list-nat)
     (function/app (function/const* 'data/nil [type-level]) nat)
     (function/lam
      [['previous nat] ['previous-range list-nat]]
      (function/app (function/const* 'data/cons [type-level])
                    nat 'previous 'previous-range))
     'upper))})

(def setlike-membership-spec
  {:name 'setlike/membership
   :kind :definition
   :universes ['u 'v]
   :transparency :reducible
   :type
   (function/forall
    [['Container type-v] ['A type-u]
     ['dictionary (function/arrow 'Container 'A 'Prop)]]
    (function/arrow 'Container 'A 'Prop))
   :value
   (function/lam
    [['Container type-v] ['A type-u]
     ['dictionary (function/arrow 'Container 'A 'Prop)]]
    'dictionary)})

(def finset-setlike-spec
  {:name 'finset/setlike
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]]
    (function/arrow
     (function/app (function/const* 'finset/Finset [U]) 'A)
     'A 'Prop))
   :value
   (function/lam
    [['A type-u]
     ['source (function/app (function/const* 'finset/Finset [U]) 'A)]
     ['value 'A]]
    (function/app
     (function/app (function/const* 'finset/to-set [U]) 'A 'source)
     'value))})

(def order-less-than-spec
  {:name 'order/less-than
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['dictionary (function/arrow 'A 'A 'Prop)]]
    (function/arrow 'A 'A 'Prop))
   :value
   (function/lam
    [['A type-u] ['dictionary (function/arrow 'A 'A 'Prop)]]
    'dictionary)})

(def order-less-or-equal-spec
  {:name 'order/less-or-equal
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['dictionary (function/arrow 'A 'A 'Prop)]]
    (function/arrow 'A 'A 'Prop))
   :value
   (function/lam
    [['A type-u] ['dictionary (function/arrow 'A 'A 'Prop)]]
    'dictionary)})

(def nat-at-most-spec
  {:name 'nat/at-most
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat 'Prop)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (proposition/existence
     type-level nat
     (function/lam
      [['extra nat]]
      (nat-equality (add 'left 'extra) 'right))))})

(def order-preorder-from-partial-spec
  {:name 'order/preorder-from-partial
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['relation (function/arrow 'A 'A 'Prop)]]
    (function/arrow 'A 'A 'Prop))
   :value
   (function/lam
    [['A type-u] ['relation (function/arrow 'A 'A 'Prop)]]
    'relation)})

(def finset-partial-order-spec
  {:name 'finset/partial-order
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]]
    (function/arrow
     (function/app (function/const* 'finset/Finset [U]) 'A)
     (function/app (function/const* 'finset/Finset [U]) 'A)
     'Prop))
   :value
   (function/lam
    [['A type-u]
     ['left (function/app (function/const* 'finset/Finset [U]) 'A)]
     ['right (function/app (function/const* 'finset/Finset [U]) 'A)]]
    (function/app (function/const* 'finset/subset [U])
                  'A 'left 'right))})

(def order-monotone-spec
  {:name 'order/monotone
   :kind :definition
   :universes ['u 'v]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['B type-v]
     ['source-order (function/arrow 'A 'A 'Prop)]
     ['target-order (function/arrow 'B 'B 'Prop)]
     ['mapping (function/arrow 'A 'B)]]
    'Prop)
   :value
   (function/lam
    [['A type-u] ['B type-v]
     ['source-order (function/arrow 'A 'A 'Prop)]
     ['target-order (function/arrow 'B 'B 'Prop)]
     ['mapping (function/arrow 'A 'B)]]
    (function/forall
     [['left 'A] ['right 'A]
      ['ordered (function/app 'source-order 'left 'right)]]
     (function/app 'target-order
                   (function/app 'mapping 'left)
                   (function/app 'mapping 'right))))})

(def member-range-successor-add-spec
  (let [claim
        (fn [value extra]
          (membership (range-list (add (succ value) extra)) value))
        motive
        (function/lam
         [['extra nat]]
         (function/forall [['value nat]] (claim 'value 'extra)))]
    {:name 'nat/member-range-successor-add
     :universes []
     :type
     (function/forall
      [['value nat] ['extra nat]] (claim 'value 'extra))
     :value
     (function/lam
      [['value nat] ['extra nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['candidate nat]]
        (let [head-case (nat-equality 'candidate (add 'candidate zero))]
          (function/app
           (function/const* 'proposition/left-disjunct [])
           head-case
           (membership (range-list (add 'candidate zero)) 'candidate)
           (function/app
            (function/const* 'equality/symmetric [type-level])
            nat (add 'candidate zero) 'candidate
            (function/app
             (function/const* 'algebra/nat-add-zero-right [])
             'candidate)))))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['candidate nat]]
        (let [prior-bound (succ (add 'candidate 'previous))
              next-bound (add 'candidate (succ 'previous))
              prior-membership
              (function/app 'induction-hypothesis 'candidate)
              same-bound
              (function/app
               (function/const* 'equality/symmetric [type-level])
               nat next-bound prior-bound
               (function/app
                (function/const* 'algebra/nat-add-successor-right [])
                'candidate 'previous))
              same-ranges
              (function/app
               (function/const* 'equality/congruent-function
                                [type-level type-level])
               nat list-nat
               (function/const* 'list/nat-range [])
               prior-bound next-bound same-bound)
              prior-proposition
              (membership (range-list prior-bound) 'candidate)
              next-proposition
              (membership (range-list next-bound) 'candidate)
              same-membership
              (proposition-congruence
               list-nat
               (function/lam
                [['enumeration list-nat]]
                (membership 'enumeration 'candidate))
               (range-list prior-bound) (range-list next-bound)
               same-ranges)
              tail-membership
              (proposition-forward prior-proposition next-proposition
                                   same-membership prior-membership)]
          (function/app
           (function/const* 'proposition/right-disjunct [])
           (nat-equality 'candidate next-bound)
           next-proposition tail-membership)))
       'extra 'value))}))

(def below-member-range-spec
  {:name 'nat/below-member-range
   :universes []
   :type
   (function/forall
    [['value nat] ['upper nat] ['evidence (below 'value 'upper)]]
    (membership (range-list 'upper) 'value))
   :value
   (function/lam
    [['value nat] ['upper nat] ['evidence (below 'value 'upper)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['extra nat]]
      (nat-equality (add (succ 'value) 'extra) 'upper))
     (membership (range-list 'upper) 'value)
     'evidence
     (function/lam
      [['extra nat]
       ['same-bound (nat-equality (add (succ 'value) 'extra) 'upper)]]
      (let [origin (add (succ 'value) 'extra)
            origin-range (range-list origin)
            target-range (range-list 'upper)
            same-ranges
            (function/app
             (function/const* 'equality/congruent-function
                              [type-level type-level])
             nat list-nat (function/const* 'list/nat-range [])
             origin 'upper 'same-bound)
            origin-proposition (membership origin-range 'value)
            target-proposition (membership target-range 'value)
            same-membership
            (proposition-congruence
             list-nat
             (function/lam
              [['enumeration list-nat]]
              (membership 'enumeration 'value))
             origin-range target-range same-ranges)]
        (proposition-forward
         origin-proposition target-proposition same-membership
         (function/app
          (function/const* 'nat/member-range-successor-add [])
          'value 'extra))))))})

(def finset-range-spec
  (let [range-set
        (function/lam [['value nat]] (below 'value 'upper))
        finset-predicate
        (function/lam
         [['source set-nat]]
         (function/app (function/const* 'set/finite [zero-level])
                       nat 'source))
        cover
        (function/lam
         [['enumeration list-nat]]
         (function/forall
          [['value nat] ['member (function/app range-set 'value)]]
          (membership 'enumeration 'value)))
        finite-range
        (witness
         type-level list-nat cover (range-list 'upper)
         (function/lam
          [['value nat] ['member (function/app range-set 'value)]]
          (function/app
           (function/const* 'nat/below-member-range [])
           'value 'upper 'member)))]
    {:name 'finset/range
     :kind :definition
     :universes []
     :transparency :reducible
     :type (function/arrow nat finset-nat)
     :value
     (function/lam
      [['upper nat]]
      (function/app
       (function/const* 'data/subtype [type-level])
       set-nat finset-predicate range-set finite-range))}))

(def member-range-equivalent-below-spec
  (let [member (function/app (to-set (range-finset 'upper)) 'value)
        bounded (below 'value 'upper)]
    {:name 'finset/member-range-equivalent-below
     :universes []
     :type
     (function/forall
      [['value nat] ['upper nat]]
      (proposition/equivalence member bounded))
     :value
     (function/lam
      [['value nat] ['upper nat]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       member bounded
       (function/lam [['evidence member]] 'evidence)
       (function/lam [['evidence bounded]] 'evidence)))}))

(def exists-nat-subset-range-spec
  (let [source-set (to-set 'source)
        cover
        (function/lam
         [['enumeration list-nat]]
         (function/forall
          [['value nat] ['member (function/app source-set 'value)]]
          (membership 'enumeration 'value)))
        result-predicate
        (function/lam
         [['upper nat]]
         (subset 'source (range-finset 'upper)))]
    {:name 'finset/exists-nat-subset-range
     :universes []
     :type
     (function/forall
      [['source finset-nat]]
      (proposition/existence type-level nat result-predicate))
     :value
     (function/lam
      [['source finset-nat]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       list-nat cover
       (proposition/existence type-level nat result-predicate)
       (finite-evidence 'source)
       (function/lam
        [['enumeration list-nat]
         ['cover-evidence (function/app cover 'enumeration)]]
        (witness
         type-level nat result-predicate
         (function/app (function/const* 'list/nat-bound []) 'enumeration)
         (function/lam
          [['value nat] ['member (function/app source-set 'value)]]
          (function/app
           (function/const* 'list/member-strictly-below-nat-bound [])
           'enumeration 'value
           (function/app 'cover-evidence 'value 'member)))))))}))

(def not-strictly-below-self-spec
  {:name 'nat/not-strictly-below-self
   :universes []
   :type
   (function/forall
    [['value nat]]
    (proposition/negation (below 'value 'value)))
   :value
   (function/lam
    [['value nat] ['evidence (below 'value 'value)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['extra nat]]
      (nat-equality (add (succ 'value) 'extra) 'value))
     (proposition/falsity) 'evidence
     (function/lam
      [['extra nat]
       ['too-large (nat-equality (add (succ 'value) 'extra) 'value)]]
      (function/app
       (function/const* 'nat/not-equal-successor-add [])
       'value 'extra
       (function/app
        (function/const* 'equality/symmetric [type-level])
        nat (add (succ 'value) 'extra) 'value 'too-large)))))})

(def not-member-range-self-spec
  {:name 'finset/not-member-range-self
   :universes []
   :type
   (function/forall
    [['value nat :implicit]]
    (proposition/negation
     (function/app (to-set (range-finset 'value)) 'value)))
   :value
   (function/lam
    [['value nat :implicit]
     ['member (function/app (to-set (range-finset 'value)) 'value)]]
    (function/app
     (function/const* 'nat/not-strictly-below-self [])
     'value 'member))})

(def member-range-proposition-equality-spec
  (let [member (function/app (to-set (range-finset 'upper)) 'value)
        bounded (below 'value 'upper)]
    {:name 'finset/member-range-proposition-equality
     :universes []
     :type
     (function/forall
      [['upper nat :implicit] ['value nat :implicit]]
      (equality 'Prop member bounded))
     :value
     (function/lam
      [['upper nat :implicit] ['value nat :implicit]]
      (function/app
       (function/const* 'equality/reflexive [proposition-level])
       'Prop member))}))

(def range-subset-of-at-most-spec
  {:name 'finset/range-subset-of-at-most
   :universes []
   :type
   (function/forall
    [['left nat :implicit] ['right nat :implicit]
     ['ordered (at-most 'left 'right) :explicit]]
    (subset (range-finset 'left) (range-finset 'right)))
   :value
   (function/lam
    [['left nat :implicit] ['right nat :implicit]
     ['ordered (at-most 'left 'right) :explicit]
     ['value nat]
     ['member (function/app (to-set (range-finset 'left)) 'value)]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['right-extra nat]]
      (nat-equality (add 'left 'right-extra) 'right))
     (below 'value 'right) 'ordered
     (function/lam
      [['right-extra nat]
       ['same-right (nat-equality (add 'left 'right-extra) 'right)]]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat
       (function/lam
        [['left-extra nat]]
        (nat-equality (add (succ 'value) 'left-extra) 'left))
       (below 'value 'right) 'member
       (function/lam
        [['left-extra nat]
         ['same-left
          (nat-equality (add (succ 'value) 'left-extra) 'left)]]
        (let [combined (add 'left-extra 'right-extra)
              start (add (succ 'value) combined)
              associated
              (add (add (succ 'value) 'left-extra) 'right-extra)
              ordered-left (add 'left 'right-extra)
              first-step
              (function/app
               (function/const* 'equality/symmetric [type-level])
               nat associated start
               (function/app
                (function/const* 'nat/add-associative [])
                (succ 'value) 'left-extra 'right-extra))
              second-step
              (function/app
               (function/const* 'equality/congruent-function
                                [type-level type-level])
               nat nat
               (function/lam
                [['candidate nat]] (add 'candidate 'right-extra))
               (add (succ 'value) 'left-extra) 'left 'same-left)
              first-two
              (function/app
               (function/const* 'equality/transitive [type-level])
               nat start associated ordered-left first-step second-step)
              complete
              (function/app
               (function/const* 'equality/transitive [type-level])
               nat start ordered-left 'right first-two 'same-right)]
          (witness
           type-level nat
           (function/lam
            [['extra nat]]
            (nat-equality (add (succ 'value) 'extra) 'right))
           combined complete)))))))})

(def at-most-of-range-subset-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]
           ['included
            (subset (range-finset 'left) (range-finset 'right))]]
          (at-most 'left 'right)))]
    {:name 'finset/at-most-of-range-subset
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]
       ['included (subset (range-finset 'left) (range-finset 'right))]]
      (at-most 'left 'right))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]
         ['ignored (subset (range-finset zero) (range-finset 'right))]]
        (witness
         type-level nat
         (function/lam
          [['extra nat]] (nat-equality (add zero 'extra) 'right))
         'right
         (function/app
          (function/const* 'equality/reflexive [type-level])
          nat 'right)))
       (function/lam
        [['previous nat]
         ['ignored-induction-hypothesis (function/app motive 'previous)]
         ['right nat]
         ['included
          (subset (range-finset (succ 'previous))
                  (range-finset 'right))]]
        (let [previous-below-successor
              (witness
               type-level nat
               (function/lam
                [['extra nat]]
                (nat-equality (add (succ 'previous) 'extra)
                              (succ 'previous)))
               zero
               (function/app
                (function/const* 'algebra/nat-add-zero-right [])
                (succ 'previous)))]
          (function/app 'included 'previous previous-below-successor)))
       'left))}))

(def range-subset-equivalent-at-most-spec
  (let [included (subset (range-finset 'left) (range-finset 'right))
        ordered (at-most 'left 'right)]
    {:name 'finset/range-subset-equivalent-at-most
     :universes []
     :type
     (function/forall
      [['left nat :implicit] ['right nat :implicit]]
      (proposition/equivalence included ordered))
     :value
     (function/lam
      [['left nat :implicit] ['right nat :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       included ordered
       (function/lam
        [['evidence included]]
        (function/app
         (function/const* 'finset/at-most-of-range-subset [])
         'left 'right 'evidence))
       (function/lam
        [['evidence ordered]]
        (function/app
         (function/const* 'finset/range-subset-of-at-most [])
         'left 'right 'evidence))))}))

(def range-monotone-spec
  {:name 'finset/range-monotone
   :universes []
   :type
   (function/app
    (function/const* 'order/monotone [zero-level zero-level])
    nat finset-nat
    (function/const* 'nat/at-most [])
    (function/app (function/const* 'finset/partial-order [zero-level]) nat)
    (function/const* 'finset/range []))
   :value
   (function/lam
    [['left nat] ['right nat] ['ordered (at-most 'left 'right)]]
    (function/app
     (function/const* 'finset/range-subset-of-at-most [])
     'left 'right 'ordered))})

(def definition-specs
  [setlike-membership-spec finset-setlike-spec
   order-less-than-spec order-less-or-equal-spec nat-at-most-spec
   order-preorder-from-partial-spec finset-partial-order-spec
   order-monotone-spec nat-range-spec finset-range-spec])

(def theorem-specs
  [member-range-successor-add-spec below-member-range-spec
   member-range-equivalent-below-spec exists-nat-subset-range-spec
   not-strictly-below-self-spec not-member-range-self-spec
   member-range-proposition-equality-spec range-subset-of-at-most-spec
   at-most-of-range-subset-spec range-subset-equivalent-at-most-spec
   range-monotone-spec])

(def constant-aliases
  {"Finset.range" 'finset/range
   "SetLike.instMembership" 'setlike/membership
   "Finset.instSetLike" 'finset/setlike
   "LT.lt" 'order/less-than
   "instLTNat" 'nat/strict-below
   "LE.le" 'order/less-or-equal
   "instLENat" 'nat/at-most
   "Monotone" 'order/monotone
   "Nat.instPreorder" 'nat/at-most
   "PartialOrder.toPreorder" 'order/preorder-from-partial
   "Finset.partialOrder" 'finset/partial-order})

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finset-range expression failed elaboration"
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
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-nat-initial-segments}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finset-range declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment [setlike-membership-spec finset-setlike-spec order-less-than-spec order-less-or-equal-spec nat-at-most-spec order-preorder-from-partial-spec finset-partial-order-spec order-monotone-spec nat-range-spec member-range-successor-add-spec below-member-range-spec finset-range-spec member-range-equivalent-below-spec exists-nat-subset-range-spec not-strictly-below-self-spec not-member-range-self-spec member-range-proposition-equality-spec range-subset-of-at-most-spec at-most-of-range-subset-spec range-subset-equivalent-at-most-spec range-monotone-spec]))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.finset.range))
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
