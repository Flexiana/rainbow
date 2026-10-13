(ns rainbow.algorithms.proofs.decision-guarantee-audit
  "Finite exact-rational decision-bound auditing as native proof data.

  Refusals are typed results of a deterministic premise checker.  They are not
  kernel claims that the underlying proposition is false; they state that the
  declared proof route is unavailable without the required evidence."
  (:refer-clojure :exclude [bound denominator numerator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value] (function/app successor value))

(defn- numeral [value]
  (nth (iterate succ zero) value))

(def one (numeral 1))
(def three (numeral 3))
(def four (numeral 4))
(def six (numeral 6))
(def ten (numeral 10))

(defn- product [left-level right-level left right]
  (function/app (function/const* 'data/Product [left-level right-level])
                left right))

(defn- pair [left-level right-level left-type right-type left right]
  (function/app (function/const* 'data/pair [left-level right-level])
                left-type right-type left right))

(defn- first-of [left-level right-level left-type right-type value]
  (function/app (function/const* 'product/first [left-level right-level])
                left-type right-type value))

(defn- second-of [left-level right-level left-type right-type value]
  (function/app (function/const* 'product/second [left-level right-level])
                left-type right-type value))

(def bool-pair (product type-level type-level bool bool))
(def bool-triple (product type-level type-level bool bool-pair))
(def premise-set (product type-level type-level bool bool-triple))

(def outcome-function-level [:max data-u data-v])
(def loss-function-level data-v)
(def loss-tail-level data-v)
(def outcome-tail-level outcome-function-level)
(def claim-level [:max outcome-function-level data-v])

(defn- premises [cap support info-field no-hindsight]
  (pair type-level type-level bool bool-triple cap
        (pair type-level type-level bool bool-pair support
              (pair type-level type-level bool bool
                    info-field no-hindsight))))

(defn- has-cap [value]
  (first-of type-level type-level bool bool-triple value))

(defn- premise-tail [value]
  (second-of type-level type-level bool bool-triple value))

(defn- has-support [value]
  (first-of type-level type-level bool bool-pair (premise-tail value)))

(defn- premise-final-pair [value]
  (second-of type-level type-level bool bool-pair (premise-tail value)))

(defn- has-info-field [value]
  (first-of type-level type-level bool bool (premise-final-pair value)))

(defn- has-no-hindsight [value]
  (second-of type-level type-level bool bool (premise-final-pair value)))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- claim-type []
  (let [actions (exact-finset-of zero-level nat)
        outcomes (function/arrow nat nat)
        loss (function/arrow nat nnrat)
        bound-and-premises
        (product type-level type-level nnrat premise-set)
        loss-tail
        (product type-level type-level loss bound-and-premises)
        outcome-tail
        (product type-level type-level outcomes loss-tail)]
    (product type-level type-level actions outcome-tail)))

(defn- enumeration [level element source]
  (function/app (function/const* 'finset-data/enumeration [level])
                element source))

(defn- list-membership [level element source value]
  (function/app (function/const* 'list/membership [level])
                element source value))

(defn- member [level element source value]
  (list-membership level element (enumeration level element source) value))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- nat-at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- base-at-most [left right]
  (function/app (function/const* 'nnrat/base-at-most []) left right))

(defn- rational-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- rational [numerator-value]
  (function/app (function/const* 'nnrat/make []) numerator-value zero))

(defn- nat-at-most-by-extra [left right extra]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['delta nat]]
                 (equality nat (add left 'delta) right))
   extra
   (function/app (function/const* 'equality/reflexive [type-level])
                 nat right)))

(def audit-result-spec
  {:block/schema-version 1
   :block/alias 'audit/AuditResult
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'audit/approved :constructor/fields []}
    {:constructor/alias 'audit/missing-cap :constructor/fields []}
    {:constructor/alias 'audit/missing-support :constructor/fields []}
    {:constructor/alias 'audit/hindsight-premise :constructor/fields []}
    {:constructor/alias 'audit/cap-exceeds-bound :constructor/fields []}]})

(def audit-result (function/const* 'audit/AuditResult []))
(def approved (function/const* 'audit/approved []))
(def missing-cap (function/const* 'audit/missing-cap []))
(def missing-support (function/const* 'audit/missing-support []))
(def hindsight-premise (function/const* 'audit/hindsight-premise []))
(def cap-exceeds-bound (function/const* 'audit/cap-exceeds-bound []))

(def premise-set-spec
  {:name 'audit/PremiseSet
   :kind :definition
   :universes []
   :type [:sort type-level]
   :value premise-set})

(def premises-spec
  {:name 'audit/premises
   :kind :definition
   :universes []
   :type (function/arrow bool bool bool bool premise-set)
   :value
   (function/lam
    [['cap bool] ['support bool] ['info-field bool] ['no-hindsight bool]]
    (premises 'cap 'support 'info-field 'no-hindsight))})

(def claim-carrier-spec
  {:name 'audit/Claim
   :kind :definition
   :universes []
   :type [:sort type-level]
   :value (claim-type)})

(def claim-spec
  (let [actions-type (exact-finset-of zero-level nat)
        outcomes-type (function/arrow nat nat)
        loss-type (function/arrow nat nnrat)
        bound-and-premises
        (product type-level type-level nnrat premise-set)
        loss-tail
        (product type-level type-level loss-type bound-and-premises)
        outcome-tail
        (product type-level type-level outcomes-type loss-tail)
        result (function/const* 'audit/Claim [])]
    {:name 'audit/claim
     :kind :definition
     :universes []
     :type
     (function/forall
      [['actions actions-type] ['outcomes outcomes-type]
       ['loss loss-type] ['bound nnrat] ['premises premise-set]]
      result)
     :value
     (function/lam
      [['actions actions-type] ['outcomes outcomes-type]
       ['loss loss-type] ['bound nnrat] ['premises premise-set]]
      (pair
       type-level type-level actions-type outcome-tail 'actions
       (pair
        type-level type-level outcomes-type loss-tail 'outcomes
        (pair type-level type-level loss-type bound-and-premises 'loss
              (pair type-level type-level nnrat premise-set
                    'bound 'premises)))))}))

(defn- accessor-spec [name accessor]
  {:name name
   :kind :definition
   :universes []
   :type (function/arrow premise-set bool)
   :value (function/lam [['value premise-set]] (accessor 'value))})

(def has-cap-spec (accessor-spec 'audit/has-cap has-cap))
(def has-support-spec (accessor-spec 'audit/has-support has-support))
(def has-info-field-spec
  (accessor-spec 'audit/has-info-field has-info-field))
(def has-no-hindsight-spec
  (accessor-spec 'audit/has-no-hindsight has-no-hindsight))

(def base-at-most-spec
  {:name 'nnrat/base-at-most
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat 'Prop)
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (nat-at-most
     (multiply (numerator 'left) (denominator 'right))
     (multiply (numerator 'right) (denominator 'left))))})

(def at-most-spec
  {:name 'nnrat/at-most
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat 'Prop)
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [predicate (function/arrow nnrat 'Prop)
          step
          (function/forall
           [['before nnrat] ['after nnrat]
            ['ordered (base-at-most 'before 'after)]
            ['before-holds (function/app 'P 'before)]]
           (function/app 'P 'after))]
      (function/forall
       [['P predicate]
        ['step step]
        ['left-holds (function/app 'P 'left)]]
       (function/app 'P 'right))))})

(def decide-nnrat-at-most-spec
  {:name 'audit/decide-nnrat-at-most
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat bool)
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (function/app
     (function/const* 'nat/decide-at-most [])
     (multiply (numerator 'left) (denominator 'right))
     (multiply (numerator 'right) (denominator 'left))))})

(defn- if-bool [motive false-case true-case decision]
  (function/app (function/const* 'data/Bool.rec [type-level])
                motive false-case true-case decision))

(def audit-decision-spec
  {:name 'audit/decision
   :kind :definition
   :universes []
   :type (function/arrow bool bool bool bool audit-result)
   :value
   (function/lam
    [['cap-present bool] ['support-present bool]
     ['no-hindsight-present bool] ['cap-within-bound bool]]
    (if-bool
     (function/lam [['ignored bool]] audit-result)
     missing-cap
     (if-bool
      (function/lam [['ignored bool]] audit-result)
      missing-support
      (if-bool
       (function/lam [['ignored bool]] audit-result)
       hindsight-premise
       (if-bool (function/lam [['ignored bool]] audit-result)
                cap-exceeds-bound approved 'cap-within-bound)
       'no-hindsight-present)
      'support-present)
     'cap-present))})

(def evaluate-spec
  {:name 'audit/evaluate
   :kind :definition
   :universes []
   :type (function/arrow premise-set nnrat nnrat audit-result)
   :value
   (function/lam
    [['premises premise-set] ['cap nnrat] ['bound nnrat]]
    (function/app
     (function/const* 'audit/decision [])
     (has-cap 'premises) (has-support 'premises)
     (has-no-hindsight 'premises)
     (function/app (function/const* 'audit/decide-nnrat-at-most [])
                   'cap 'bound)))})

(def action-space-spec
  {:name 'audit-ex/action-space
   :kind :definition
   :universes []
   :type (exact-finset-of zero-level nat)
   :value (function/app (function/const* 'finset-data/range []) three)})

(def outcome-support-spec
  {:name 'audit-ex/outcome-support
   :kind :definition
   :universes []
   :type (exact-finset-of zero-level nat)
   :value (function/app (function/const* 'finset-data/range []) three)})

(defn- named-nat-spec [name value]
  {:name name :kind :definition :universes [] :type nat :value value})

(def accept-spec (named-nat-spec 'audit-ex/accept zero))
(def renegotiate-spec (named-nat-spec 'audit-ex/renegotiate one))
(def decline-spec (named-nat-spec 'audit-ex/decline (numeral 2)))

(def outcomes-spec
  {:name 'audit-ex/outcomes
   :kind :definition
   :universes []
   :type (function/arrow nat nat)
   :value (function/lam [['action nat]] 'action)})

(def loss-spec
  {:name 'audit-ex/loss
   :kind :definition
   :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['outcome nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     (rational ten)
     (function/lam
      [['previous nat] ['ignored-previous-loss nnrat]]
      (function/app
       (function/const* 'data/Nat.rec [type-level])
       (function/lam [['ignored nat]] nnrat)
       (rational four)
       (function/lam
        [['ignored-previous nat] ['ignored-loss nnrat]]
        (rational zero))
       'previous))
     'outcome))})

(def cap-ten-spec (named-nat-spec 'audit-ex/cap-numerator ten))

(def rational-ten-spec
  {:name 'audit-ex/ten
   :kind :definition :universes [] :type nnrat :value (rational ten)})

(def rational-three-spec
  {:name 'audit-ex/three
   :kind :definition :universes [] :type nnrat :value (rational three)})

(def complete-premises-spec
  {:name 'audit-ex/complete-premises
   :kind :definition :universes [] :type premise-set
   :value (premises true-value true-value false-value true-value)})

(def missing-cap-premises-spec
  {:name 'audit-ex/missing-cap-premises
   :kind :definition :universes [] :type premise-set
   :value (premises false-value true-value false-value true-value)})

(def missing-support-premises-spec
  {:name 'audit-ex/missing-support-premises
   :kind :definition :universes [] :type premise-set
   :value (premises true-value false-value false-value true-value)})

(defn- claim-instance-spec [name premises-name bound-name]
  {:name name :kind :definition :universes []
   :type (function/const* 'audit/Claim [])
   :value
   (function/app
    (function/const* 'audit/claim [])
    (function/const* 'audit-ex/action-space [])
    (function/const* 'audit-ex/outcomes [])
    (function/const* 'audit-ex/loss [])
    (function/const* bound-name [])
    (function/const* premises-name []))})

(def audit-ex-1-claim-spec
  (claim-instance-spec 'audit-ex-1/claim
                       'audit-ex/complete-premises 'audit-ex/ten))
(def audit-ex-2-claim-spec
  (claim-instance-spec 'audit-ex-2/claim
                       'audit-ex/missing-cap-premises 'audit-ex/ten))
(def audit-ex-3-claim-spec
  (claim-instance-spec 'audit-ex-3/claim
                       'audit-ex/complete-premises 'audit-ex/three))
(def audit-ex-4-claim-spec
  (claim-instance-spec 'audit-ex-4/claim
                       'audit-ex/missing-support-premises 'audit-ex/ten))

(defn- evaluation [premises-name bound-name]
  (function/app (function/const* 'audit/evaluate [])
                (function/const* premises-name [])
                (function/const* 'audit-ex/ten [])
                (function/const* bound-name [])))

(defn- result-spec [name premises-name bound-name]
  {:name name :kind :definition :universes [] :type audit-result
   :value (evaluation premises-name bound-name)})

(def audit-ex-1-result-spec
  (result-spec 'audit-ex-1/result 'audit-ex/complete-premises 'audit-ex/ten))
(def audit-ex-2-result-spec
  (result-spec 'audit-ex-2/result 'audit-ex/missing-cap-premises 'audit-ex/ten))
(def audit-ex-3-result-spec
  (result-spec 'audit-ex-3/result 'audit-ex/complete-premises 'audit-ex/three))
(def audit-ex-4-result-spec
  (result-spec 'audit-ex-4/result 'audit-ex/missing-support-premises
               'audit-ex/ten))

(def definition-specs
  [premise-set-spec premises-spec claim-carrier-spec claim-spec
   has-cap-spec has-support-spec
   has-info-field-spec has-no-hindsight-spec base-at-most-spec at-most-spec
   decide-nnrat-at-most-spec audit-decision-spec evaluate-spec
   action-space-spec outcome-support-spec accept-spec renegotiate-spec
   decline-spec outcomes-spec loss-spec cap-ten-spec rational-ten-spec
   rational-three-spec complete-premises-spec missing-cap-premises-spec
   missing-support-premises-spec
   audit-ex-1-claim-spec audit-ex-2-claim-spec audit-ex-3-claim-spec
   audit-ex-4-claim-spec audit-ex-1-result-spec audit-ex-2-result-spec
   audit-ex-3-result-spec audit-ex-4-result-spec])

(def at-most-from-cross-spec
  (let [predicate (function/arrow nnrat 'Prop)
        step
        (function/forall
         [['before nnrat] ['after nnrat]
          ['ordered (base-at-most 'before 'after)]
          ['before-holds (function/app 'P 'before)]]
         (function/app 'P 'after))]
    {:name 'nnrat/at-most-from-cross
     :universes []
     :type
     (function/forall
      [['left nnrat] ['right nnrat]
       ['ordered (base-at-most 'left 'right)]]
      (rational-at-most 'left 'right))
     :value
     (function/lam
      [['left nnrat] ['right nnrat]
       ['ordered (base-at-most 'left 'right)]
       ['P predicate] ['step step]
       ['left-holds (function/app 'P 'left)]]
      (function/app 'step 'left 'right 'ordered 'left-holds))}))

(def at-most-reflexive-spec
  (let [predicate (function/arrow nnrat 'Prop)
        step
        (function/forall
         [['before nnrat] ['after nnrat]
          ['ordered (base-at-most 'before 'after)]
          ['before-holds (function/app 'P 'before)]]
         (function/app 'P 'after))]
    {:name 'nnrat/at-most-reflexive
     :universes []
     :type (function/forall [['value nnrat]]
                            (rational-at-most 'value 'value))
     :value
     (function/lam
      [['value nnrat] ['P predicate] ['ignored-step step]
       ['value-holds (function/app 'P 'value)]]
      'value-holds)}))

(def at-most-transitive-spec
  (let [predicate (function/arrow nnrat 'Prop)
        step
        (function/forall
         [['before nnrat] ['after nnrat]
          ['ordered (base-at-most 'before 'after)]
          ['before-holds (function/app 'P 'before)]]
         (function/app 'P 'after))]
    {:name 'nnrat/at-most-transitive
     :universes []
     :type
     (function/forall
      [['left nnrat] ['middle nnrat] ['right nnrat]
       ['first (rational-at-most 'left 'middle)]
       ['second (rational-at-most 'middle 'right)]]
      (rational-at-most 'left 'right))
     :value
     (function/lam
      [['left nnrat] ['middle nnrat] ['right nnrat]
       ['first (rational-at-most 'left 'middle)]
       ['second (rational-at-most 'middle 'right)]
       ['P predicate] ['step step]
       ['left-holds (function/app 'P 'left)]]
      (function/app
       'second 'P 'step
       (function/app 'first 'P 'step 'left-holds)))}))

(def soundness-spec
  (let [action-member (member U 'Action 'actions 'action)
        outcome-member
        (member V 'Outcome 'support (function/app 'outcomes 'action))
        cap-law
        (function/forall
         [['action 'Action] ['member action-member]]
         (rational-at-most
          (function/app 'loss (function/app 'outcomes 'action)) 'cap))
        support-law
        (function/forall
         [['action 'Action] ['member action-member]] outcome-member)
        result
        (function/forall
         [['action 'Action] ['member action-member]]
         (rational-at-most
          (function/app 'loss (function/app 'outcomes 'action)) 'bound))]
    {:name 'audit/decision-guarantee-sound
     :universes ['u 'v]
     :type
     (function/forall
      [['Action type-u] ['Outcome type-v]
       ['actions (exact-finset-of U 'Action)]
       ['outcomes (function/arrow 'Action 'Outcome)]
       ['loss (function/arrow 'Outcome nnrat)]
       ['bound nnrat] ['premises premise-set]
       ['cap nnrat] ['support (exact-finset-of V 'Outcome)]
       ['cap-present (equality bool (has-cap 'premises) true-value)]
       ['support-present
        (equality bool (has-support 'premises) true-value)]
       ['no-hindsight-present
        (equality bool (has-no-hindsight 'premises) true-value)]
       ['cap-law cap-law] ['support-law support-law]
       ['cap-within-bound (rational-at-most 'cap 'bound)]]
      result)
     :value
     (function/lam
      [['Action type-u] ['Outcome type-v]
       ['actions (exact-finset-of U 'Action)]
       ['outcomes (function/arrow 'Action 'Outcome)]
       ['loss (function/arrow 'Outcome nnrat)]
       ['bound nnrat] ['premises premise-set]
       ['cap nnrat] ['support (exact-finset-of V 'Outcome)]
       ['ignored-cap-present (equality bool (has-cap 'premises) true-value)]
       ['ignored-support-present
        (equality bool (has-support 'premises) true-value)]
       ['ignored-no-hindsight-present
        (equality bool (has-no-hindsight 'premises) true-value)]
       ['cap-law cap-law] ['ignored-support-law support-law]
       ['cap-within-bound (rational-at-most 'cap 'bound)]
       ['action 'Action] ['member action-member]]
      (function/app
       (function/const* 'nnrat/at-most-transitive [])
       (function/app 'loss (function/app 'outcomes 'action))
       'cap 'bound
       (function/app 'cap-law 'action 'member)
       'cap-within-bound))}))

(def refusal-path-spec
  (let [raw-decision (fn [cap support hindsight ordered]
                       (function/app (function/const* 'audit/decision [])
                                     cap support hindsight ordered))
        missing-cap-law
        (equality audit-result
                  (raw-decision false-value 'support 'hindsight 'ordered)
                  missing-cap)
        missing-support-law
        (equality audit-result
                  (raw-decision true-value false-value 'hindsight 'ordered)
                  missing-support)
        hindsight-law
        (equality audit-result
                  (raw-decision true-value true-value false-value 'ordered)
                  hindsight-premise)
        cap-exceeds-law
        (equality audit-result
                  (raw-decision true-value true-value true-value false-value)
                  cap-exceeds-bound)]
    {:name 'audit/refusal-path
     :universes []
     :type
     (function/forall
      [['support bool] ['hindsight bool] ['ordered bool]]
      (proposition/conjunction
       missing-cap-law
       (proposition/conjunction
        missing-support-law
        (proposition/conjunction hindsight-law cap-exceeds-law))))
     :value
     (function/lam
      [['support bool] ['hindsight bool] ['ordered bool]]
      (function/app
       (function/const* 'proposition/conjoin [])
       missing-cap-law
       (proposition/conjunction
        missing-support-law
        (proposition/conjunction hindsight-law cap-exceeds-law))
       (function/app (function/const* 'equality/reflexive [type-level])
                     audit-result missing-cap)
       (function/app
        (function/const* 'proposition/conjoin [])
        missing-support-law
        (proposition/conjunction hindsight-law cap-exceeds-law)
        (function/app (function/const* 'equality/reflexive [type-level])
                      audit-result missing-support)
        (function/app
         (function/const* 'proposition/conjoin [])
         hindsight-law cap-exceeds-law
         (function/app (function/const* 'equality/reflexive [type-level])
                       audit-result hindsight-premise)
         (function/app (function/const* 'equality/reflexive [type-level])
                       audit-result cap-exceeds-bound)))))}))

(def loss-at-most-ten-spec
  (let [loss (function/const* 'audit-ex/loss [])
        cap (function/const* 'audit-ex/ten [])
        motive
        (function/lam
         [['outcome nat]]
         (rational-at-most (function/app loss 'outcome) cap))
        four-rational (rational four)
        zero-rational (rational zero)
        four-to-ten
        (function/app
         (function/const* 'nnrat/at-most-from-cross [])
         four-rational cap
         (nat-at-most-by-extra four ten six))
        zero-to-ten
        (function/app
         (function/const* 'nnrat/at-most-from-cross [])
         zero-rational cap
         (nat-at-most-by-extra zero ten ten))]
    {:name 'audit-ex/loss-at-most-ten
     :universes []
     :type (function/forall [['outcome nat]]
                            (function/app motive 'outcome))
     :value
     (function/lam
      [['outcome nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/app (function/const* 'nnrat/at-most-reflexive []) cap)
       (function/lam
        [['previous nat]
         ['ignored-induction-hypothesis (function/app motive 'previous)]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam [['inner nat]]
                       (function/app motive (succ 'inner)))
         four-to-ten
         (function/lam
          [['ignored-inner nat] ['ignored-proof
                                  (function/app motive
                                                (succ 'ignored-inner))]]
          zero-to-ten)
         'previous))
       'outcome))}))

(def audit-ex-1-proof-spec
  (let [actions (function/const* 'audit-ex/action-space [])
        outcomes (function/const* 'audit-ex/outcomes [])
        loss (function/const* 'audit-ex/loss [])
        bound (function/const* 'audit-ex/ten [])
        premises-value (function/const* 'audit-ex/complete-premises [])
        support (function/const* 'audit-ex/outcome-support [])
        action-member (member zero-level nat actions 'action)
        result
        (function/forall
         [['action nat] ['member action-member]]
         (rational-at-most
          (function/app loss (function/app outcomes 'action)) bound))]
    {:name 'audit-ex-1/all-losses-at-most-ten
     :universes []
     :type result
     :value
     (function/app
      (function/const* 'audit/decision-guarantee-sound
                       [zero-level zero-level])
      nat nat actions outcomes loss bound premises-value bound support
      (function/app (function/const* 'equality/reflexive [type-level])
                    bool true-value)
      (function/app (function/const* 'equality/reflexive [type-level])
                    bool true-value)
      (function/app (function/const* 'equality/reflexive [type-level])
                    bool true-value)
      (function/lam
       [['action nat] ['ignored-member action-member]]
       (function/app (function/const* 'audit-ex/loss-at-most-ten [])
                     'action))
      (function/lam [['action nat] ['member action-member]] 'member)
      (function/app (function/const* 'nnrat/at-most-reflexive []) bound))}))

(defn- result-theorem-spec [name result-name expected]
  {:name name
   :universes []
   :type (equality audit-result (function/const* result-name []) expected)
   :value
   (function/app (function/const* 'equality/reflexive [type-level])
                 audit-result expected)})

(def audit-ex-1-result-theorem-spec
  (result-theorem-spec 'audit-ex-1/audit-approved
                       'audit-ex-1/result approved))
(def audit-ex-2-result-theorem-spec
  (result-theorem-spec 'audit-ex-2/refused-missing-cap
                       'audit-ex-2/result missing-cap))
(def audit-ex-3-result-theorem-spec
  (result-theorem-spec 'audit-ex-3/refused-cap-exceeds-bound
                       'audit-ex-3/result cap-exceeds-bound))
(def audit-ex-4-result-theorem-spec
  (result-theorem-spec 'audit-ex-4/refused-missing-support
                       'audit-ex-4/result missing-support))

(def theorem-specs
  [at-most-from-cross-spec at-most-reflexive-spec at-most-transitive-spec
   soundness-spec refusal-path-spec loss-at-most-ten-spec
   audit-ex-1-proof-spec audit-ex-1-result-theorem-spec
   audit-ex-2-result-theorem-spec audit-ex-3-result-theorem-spec
   audit-ex-4-result-theorem-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Decision-guarantee audit expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :decision-guarantee-audit-v0}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Decision-guarantee audit declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (let [block (environment/resolve-id checked-environment 'audit/AuditResult) installed (every? #(environment/resolve-id checked-environment (:name %)) (concat definition-specs theorem-specs))] (cond (and block installed) checked-environment (or block installed) (throw (ex-info "Decision-guarantee package is partially installed" {:result-block? (boolean block) :declarations-complete? installed})) :else (let [added (kernel/add-inductive-block checked-environment audit-result-spec)] (when-not (= :accepted (:status added)) (throw (ex-info "AuditResult inductive block rejected" {:result added}))) (reduce add-spec (:environment added) (concat definition-specs theorem-specs))))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.decision-guarantee-audit))
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

(defn block-id [checked-environment]
  (environment/resolve-id checked-environment 'audit/AuditResult))
