(ns rainbow.math.finite.policy-evaluation
  "AHoF D20: bounded finite-policy evaluation over exact rational data."
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
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value] (function/app successor value))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [U])
                element source value))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- bellman [element source transition reward discount value state]
  (function/app
   (function/const* 'bellman/nnrat-fixed-policy [U])
   element source transition reward discount value state))

(defn- iterate-value
  [element source transition reward discount steps initial]
  (let [value-function (function/arrow element nnrat)]
    (function/app
     (function/const* 'data/Nat.rec [data-level])
     (function/lam [['ignored nat]] value-function)
     initial
     (function/lam
      [['ignored-step nat] ['previous-value value-function]]
      (function/lam
       [['state element]]
       (bellman element source transition reward discount
                'previous-value 'state)))
     steps)))

(defn- pointwise-equivalent [element left right]
  (function/forall
   [['state element]]
   (equivalent (function/app left 'state) (function/app right 'state))))

(defn- transition-equivalent [element left right]
  (function/forall
   [['state element] ['next element]]
   (equivalent (function/app left 'state 'next)
               (function/app right 'state 'next))))

(defn- reflexive-equivalent [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(def recursor-successor-spec
  (let [recursor
        (fn [carrier initial step count]
          (function/app
           (function/const* 'data/Nat.rec [data-level])
           (function/lam [['ignored nat]] carrier)
           initial step count))]
    {:name 'nat/recursor-successor-constant
     :universes ['u]
     :type
     (function/forall
      [['C type-u] ['initial 'C]
       ['step (function/arrow nat 'C 'C)] ['count nat]]
      (function/equality
       data-level 'C
       (recursor 'C 'initial 'step (succ 'count))
       (function/app 'step 'count
                     (recursor 'C 'initial 'step 'count))))
     :value
     (function/lam
      [['C type-u] ['initial 'C]
       ['step (function/arrow nat 'C 'C)] ['count nat]]
      (function/app
       (function/const* 'equality/reflexive [data-level])
       'C
       (function/app 'step 'count
                     (recursor 'C 'initial 'step 'count))))}))

(def successor-spec
  (let [previous
        (iterate-value 'A 'source 'transition 'reward 'discount
                       'steps 'initial)
        next
        (iterate-value 'A 'source 'transition 'reward 'discount
                       (succ 'steps) 'initial)
        value-function (function/arrow 'A nnrat)
        step
        (function/lam
         [['ignored-step nat]
          ['previous-value value-function]]
         (function/lam
          [['candidate 'A]]
          (bellman 'A 'source 'transition 'reward 'discount
                   'previous-value 'candidate)))]
    {:name 'bellman/nnrat-value-iterate-successor
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['steps nat] ['initial (function/arrow 'A nnrat)]]
      (function/equality
       data-level value-function next
       (function/app step 'steps previous)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['steps nat] ['initial (function/arrow 'A nnrat)]]
      (function/app
       (function/const* 'nat/recursor-successor-constant [U])
       value-function 'initial step 'steps))}))

(def iterate-related-spec
  (let [recursor
        (fn [carrier initial step count]
          (function/app
           (function/const* 'data/Nat.rec [data-level])
           (function/lam [['ignored nat]] carrier)
           initial step count))
        motive
        (function/lam
         [['count nat]]
         (function/app
          'R
          (recursor 'C 'left-initial 'left-step 'count)
          (recursor 'C 'right-initial 'right-step 'count)))]
    {:name 'nat/iterate-related
     :universes ['u]
     :type
     (function/forall
      [['C type-u] ['R (function/arrow 'C 'C 'Prop)]
       ['left-initial 'C] ['right-initial 'C]
       ['left-step (function/arrow nat 'C 'C)]
       ['right-step (function/arrow nat 'C 'C)]
       ['same-initial (function/app 'R 'left-initial 'right-initial)]
       ['same-step
        (function/forall
         [['count nat] ['left 'C] ['right 'C]
          ['same (function/app 'R 'left 'right)]]
         (function/app 'R
                       (function/app 'left-step 'count 'left)
                       (function/app 'right-step 'count 'right)))]
       ['count nat]]
      (function/app motive 'count))
     :value
     (function/lam
      [['C type-u] ['R (function/arrow 'C 'C 'Prop)]
       ['left-initial 'C] ['right-initial 'C]
       ['left-step (function/arrow nat 'C 'C)]
       ['right-step (function/arrow nat 'C 'C)]
       ['same-initial (function/app 'R 'left-initial 'right-initial)]
       ['same-step
        (function/forall
         [['count nat] ['left 'C] ['right 'C]
          ['same (function/app 'R 'left 'right)]]
         (function/app 'R
                       (function/app 'left-step 'count 'left)
                       (function/app 'right-step 'count 'right)))]
       ['count nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive 'same-initial
       (function/lam
        [['previous nat] ['induction-hypothesis (function/app motive 'previous)]]
        (function/app
         'same-step 'previous
         (recursor 'C 'left-initial 'left-step 'previous)
         (recursor 'C 'right-initial 'right-step 'previous)
         'induction-hypothesis))
       'count))}))

(def iterate-congruent-spec
  (let [left-value
        (iterate-value 'A 'source 'transition 'reward 'discount
                       'steps 'initial)
        right-value
        (iterate-value 'A 'source 'equivalent-transition
                       'equivalent-reward 'equivalent-discount
                       'steps 'equivalent-initial)
        value-function (function/arrow 'A nnrat)
        relation
        (function/lam
         [['left value-function] ['right value-function]]
         (pointwise-equivalent 'A 'left 'right))
        left-step
        (function/lam
         [['ignored nat] ['value value-function]]
         (function/lam
          [['state 'A]]
          (bellman 'A 'source 'transition 'reward 'discount 'value 'state)))
        right-step
        (function/lam
         [['ignored nat] ['value value-function]]
         (function/lam
          [['state 'A]]
          (bellman 'A 'source 'equivalent-transition 'equivalent-reward
                   'equivalent-discount 'value 'state)))]
    {:name 'bellman/nnrat-value-iterate-congruent
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['equivalent-initial (function/arrow 'A nnrat)]
       ['same-transition
        (transition-equivalent 'A 'transition 'equivalent-transition)]
       ['same-reward (pointwise-equivalent 'A 'reward 'equivalent-reward)]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['same-initial
        (pointwise-equivalent 'A 'initial 'equivalent-initial)]
       ['steps nat] ['state 'A]]
      (equivalent (function/app left-value 'state)
                  (function/app right-value 'state)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['equivalent-initial (function/arrow 'A nnrat)]
       ['same-transition
        (transition-equivalent 'A 'transition 'equivalent-transition)]
       ['same-reward (pointwise-equivalent 'A 'reward 'equivalent-reward)]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['same-initial
        (pointwise-equivalent 'A 'initial 'equivalent-initial)]
       ['steps nat]]
      (function/app
       (function/const* 'nat/iterate-related [U])
       value-function relation 'initial 'equivalent-initial
       left-step right-step 'same-initial
       (function/lam
        [['ignored nat] ['left value-function] ['right value-function]
         ['same (pointwise-equivalent 'A 'left 'right)]
         ['state 'A]]
        (function/app
         (function/const* 'bellman/nnrat-fixed-policy-congruent [U])
         'A 'source 'transition 'equivalent-transition
         'reward 'equivalent-reward 'discount 'equivalent-discount
         'left 'right 'same-transition 'same-reward 'same-discount
         'same 'state))
       'steps))}))

(def model-transfer-spec
  (let [value (iterate-value 'A 'source 'transition 'reward 'discount
                             'steps 'initial)
        equivalent-value
        (iterate-value 'A 'source 'equivalent-transition
                       'equivalent-reward 'equivalent-discount
                       'steps 'initial)]
    {:name 'bellman/nnrat-value-iterate-model-transfer
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['same-transition
        (transition-equivalent 'A 'transition 'equivalent-transition)]
       ['same-reward (pointwise-equivalent 'A 'reward 'equivalent-reward)]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['steps nat] ['state 'A]]
      (equivalent (function/app value 'state)
                  (function/app equivalent-value 'state)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['same-transition
        (transition-equivalent 'A 'transition 'equivalent-transition)]
       ['same-reward (pointwise-equivalent 'A 'reward 'equivalent-reward)]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['steps nat] ['state 'A]]
      (function/app
       (function/const* 'bellman/nnrat-value-iterate-congruent [U])
       'A 'source 'transition 'equivalent-transition
       'reward 'equivalent-reward 'discount 'equivalent-discount
       'initial 'initial 'same-transition 'same-reward 'same-discount
       (function/lam [['candidate 'A]]
                     (reflexive-equivalent
                      (function/app 'initial 'candidate)))
       'steps 'state))}))

(def initial-transfer-spec
  (let [value (iterate-value 'A 'source 'transition 'reward 'discount
                             'steps 'initial)
        equivalent-value
        (iterate-value 'A 'source 'transition 'reward 'discount
                       'steps 'equivalent-initial)]
    {:name 'bellman/nnrat-value-iterate-initial-transfer
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['equivalent-initial (function/arrow 'A nnrat)]
       ['same-initial
        (pointwise-equivalent 'A 'initial 'equivalent-initial)]
       ['steps nat] ['state 'A]]
      (equivalent (function/app value 'state)
                  (function/app equivalent-value 'state)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['initial (function/arrow 'A nnrat)]
       ['equivalent-initial (function/arrow 'A nnrat)]
       ['same-initial
        (pointwise-equivalent 'A 'initial 'equivalent-initial)]
       ['steps nat] ['state 'A]]
      (function/app
       (function/const* 'bellman/nnrat-value-iterate-congruent [U])
       'A 'source 'transition 'transition 'reward 'reward
       'discount 'discount 'initial 'equivalent-initial
       (function/lam
        [['current 'A] ['next 'A]]
        (reflexive-equivalent (function/app 'transition 'current 'next)))
       (function/lam [['candidate 'A]]
                     (reflexive-equivalent
                      (function/app 'reward 'candidate)))
       (reflexive-equivalent 'discount) 'same-initial 'steps 'state))}))

(def theorem-specs
  [recursor-successor-spec successor-spec iterate-related-spec
   iterate-congruent-spec model-transfer-spec
   initial-transfer-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite policy-evaluation expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
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
          {:origin :native :producer :finite-policy-evaluation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite policy-evaluation declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.policy-evaluation))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
