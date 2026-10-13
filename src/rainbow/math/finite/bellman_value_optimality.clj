(ns rainbow.math.finite.bellman-value-optimality
  "Normalized finite NNRAT expectation bounds and Bellman contractions.

  Transition normalization is expressed directly as equivalence of each
  finite row total with nnrat/one.  All additive estimates are subtraction
  free.  The optimality-step proof delegates finite-argmax transport to the
  opaque unfold-based nonexpansiveness theorem.  Native and axiom-free on D63."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-monotone :as monotone]
            [rainbow.math.finite.bellman-optimal-contraction :as optimal]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.map-sum-respects :as map-respects]
            [rainbow.math.rational.nnrat.map-sum-scale :as map-scale]
            [rainbow.math.rational.nnrat.general-contraction :as general-contraction]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
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
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- succ [value]
  (function/app successor value))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'nnrat/map-sum [U])
                element mapping source))

(defn- expectation [element source mass value]
  (function/app (function/const* 'probability/nnrat-expectation [U])
                element source mass value))

(defn- total-mass [element source mass]
  (function/app (function/const* 'probability/nnrat-total-mass [U])
                element source mass))

(defn- rows-normalized
  [state action states transition]
  (function/app (function/const* 'markov/nnrat-rows-normalized [U V])
                state action states transition))

(defn- action-backup
  [state action states transition reward discount value current chosen]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount value current chosen))

(defn- backup-operator
  [state action states transition reward discount]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount))

(defn- optimality-step
  [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(defn- contraction-radius [discount initial-error steps]
  (function/app (function/const* 'value/nnrat-contraction-radius [])
                discount initial-error steps))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))

(defn- equivalent-transitive [left middle right first-step second-step]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first-step second-step))

(defn- add-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left equivalent-left right equivalent-right
                same-left same-right))

(defn- multiply-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence [])
                left equivalent-left right equivalent-right
                same-left same-right))

(def total-mass-spec
  {:name 'probability/nnrat-total-mass
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]]
    nnrat)
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]]
    (map-sum 'A 'mass (enumeration 'A 'source)))})

(def rows-normalized-spec
  {:name 'markov/nnrat-rows-normalized
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]]
    (function/forall
     [['state 'S] ['action 'A]]
     (equivalent
      (total-mass 'S 'states (function/app 'transition 'state 'action))
      nnrat-one)))})

(def contraction-radius-spec
  {:name 'value/nnrat-contraction-radius
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nat nnrat)
   :value
   (function/lam
    [['discount nnrat] ['initial-error nnrat] ['steps nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     'initial-error
     (function/lam
      [['ignored-step nat] ['previous-radius nnrat]]
      (multiply 'discount 'previous-radius))
     'steps))})

(def multiply-distributes-add-left-spec
  {:name 'nnrat/multiply-distributes-add-left
   :universes []
   :type
   (function/forall
    [['factor nnrat] ['left nnrat] ['right nnrat]]
    (equivalent
     (multiply 'factor (add 'left 'right))
     (add (multiply 'factor 'left) (multiply 'factor 'right))))
   :value
   (function/lam
    [['factor nnrat] ['left nnrat] ['right nnrat]]
    (let [start (multiply 'factor (add 'left 'right))
          commuted (multiply (add 'left 'right) 'factor)
          distributed
          (add (multiply 'left 'factor) (multiply 'right 'factor))
          finish
          (add (multiply 'factor 'left) (multiply 'factor 'right))
          commute-product
          (function/app (function/const* 'nnrat/multiply-commutative [])
                        'factor (add 'left 'right))
          distribute
          (function/app
           (function/const* 'nnrat/multiply-distributes-add-right [])
           'left 'right 'factor)
          commute-terms
          (add-respects
           (multiply 'left 'factor) (multiply 'factor 'left)
           (multiply 'right 'factor) (multiply 'factor 'right)
           (function/app (function/const* 'nnrat/multiply-commutative [])
                         'left 'factor)
           (function/app (function/const* 'nnrat/multiply-commutative [])
                         'right 'factor))]
      (equivalent-transitive
       start commuted finish commute-product
       (equivalent-transitive
        commuted distributed finish distribute commute-terms))))})

(def expectation-add-constant-spec
  {:name 'probability/nnrat-expectation-add-constant
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['value (function/arrow 'A nnrat)]
     ['epsilon nnrat]]
    (equivalent
     (expectation
      'A 'source 'mass
      (function/lam [['state 'A]]
                    (add (function/app 'value 'state) 'epsilon)))
     (add (expectation 'A 'source 'mass 'value)
          (multiply (total-mass 'A 'source 'mass) 'epsilon))))
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['value (function/arrow 'A nnrat)]
     ['epsilon nnrat]]
    (let [items (enumeration 'A 'source)
          shifted-products
          (function/lam
           [['state 'A]]
           (multiply (add (function/app 'value 'state) 'epsilon)
                     (function/app 'mass 'state)))
          split-products
          (function/lam
           [['state 'A]]
           (add (multiply (function/app 'value 'state)
                          (function/app 'mass 'state))
                (multiply 'epsilon (function/app 'mass 'state))))
          value-products
          (function/lam
           [['state 'A]]
           (multiply (function/app 'value 'state)
                     (function/app 'mass 'state)))
          epsilon-products
          (function/lam
           [['state 'A]]
           (multiply 'epsilon (function/app 'mass 'state)))
          right-scaled-mass
          (function/lam
           [['state 'A]]
           (multiply (function/app 'mass 'state) 'epsilon))
          shifted-sum (map-sum 'A shifted-products items)
          split-sum (map-sum 'A split-products items)
          value-sum (map-sum 'A value-products items)
          epsilon-sum (map-sum 'A epsilon-products items)
          right-scaled-sum (map-sum 'A right-scaled-mass items)
          total (total-mass 'A 'source 'mass)
          split-pointwise
          (function/lam
           [['state 'A]]
           (function/app
            (function/const* 'nnrat/multiply-distributes-add-right [])
            (function/app 'value 'state) 'epsilon
            (function/app 'mass 'state)))
          expose-split
          (function/app
           (function/const* 'nnrat/map-sum-respects-equivalence [U])
           'A shifted-products split-products split-pointwise items)
          split-sums
          (function/app (function/const* 'nnrat/map-sum-add [U])
                        'A value-products epsilon-products items)
          commute-pointwise
          (function/lam
           [['state 'A]]
           (function/app (function/const* 'nnrat/multiply-commutative [])
                         'epsilon (function/app 'mass 'state)))
          commute-sum
          (function/app
           (function/const* 'nnrat/map-sum-respects-equivalence [U])
           'A epsilon-products right-scaled-mass commute-pointwise items)
          expose-right-scaled
          (add-respects
           value-sum value-sum epsilon-sum right-scaled-sum
           (equivalent-reflexive value-sum) commute-sum)
          scale-out
          (function/app (function/const* 'nnrat/map-sum-scale-right [U])
                        'A 'mass 'epsilon items)
          collect-scale
          (add-respects
           value-sum value-sum right-scaled-sum (multiply total 'epsilon)
           (equivalent-reflexive value-sum)
           (equivalent-symmetric
            (multiply total 'epsilon) right-scaled-sum scale-out))]
      (equivalent-transitive
       shifted-sum split-sum
       (add value-sum (multiply total 'epsilon))
       expose-split
       (equivalent-transitive
        split-sum (add value-sum epsilon-sum)
        (add value-sum (multiply total 'epsilon))
        split-sums
        (equivalent-transitive
         (add value-sum epsilon-sum)
         (add value-sum right-scaled-sum)
         (add value-sum (multiply total 'epsilon))
         expose-right-scaled collect-scale)))))})

(def expectation-additive-upper-bound-normalized-spec
  {:name 'probability/nnrat-expectation-additive-upper-bound-normalized
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['normalized
      (equivalent (total-mass 'A 'source 'mass) nnrat-one)]
     ['lower-value (function/arrow 'A nnrat)]
     ['upper-value (function/arrow 'A nnrat)]
     ['epsilon nnrat]
     ['pointwise
      (function/forall
       [['state 'A]]
       (at-most (function/app 'lower-value 'state)
                (add (function/app 'upper-value 'state) 'epsilon)))]]
    (at-most (expectation 'A 'source 'mass 'lower-value)
             (add (expectation 'A 'source 'mass 'upper-value) 'epsilon)))
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['normalized
      (equivalent (total-mass 'A 'source 'mass) nnrat-one)]
     ['lower-value (function/arrow 'A nnrat)]
     ['upper-value (function/arrow 'A nnrat)]
     ['epsilon nnrat]
     ['pointwise
      (function/forall
       [['state 'A]]
       (at-most (function/app 'lower-value 'state)
                (add (function/app 'upper-value 'state) 'epsilon)))]]
    (let [shifted-value
          (function/lam
           [['state 'A]]
           (add (function/app 'upper-value 'state) 'epsilon))
          lower-expectation
          (expectation 'A 'source 'mass 'lower-value)
          shifted-expectation
          (expectation 'A 'source 'mass shifted-value)
          upper-expectation
          (expectation 'A 'source 'mass 'upper-value)
          total (total-mass 'A 'source 'mass)
          target (add upper-expectation 'epsilon)
          expectation-ordered
          (function/app
           (function/const* 'probability/nnrat-expectation-monotone [U])
           'A 'source 'mass 'lower-value shifted-value 'pointwise)
          affine
          (function/app
           (function/const* 'probability/nnrat-expectation-add-constant [U])
           'A 'source 'mass 'upper-value 'epsilon)
          normalize-product
          (multiply-respects
           total nnrat-one 'epsilon 'epsilon
           'normalized (equivalent-reflexive 'epsilon))
          one-product
          (function/app (function/const* 'nnrat/multiply-one-left [])
                        'epsilon)
          normalized-product
          (equivalent-transitive
           (multiply total 'epsilon) (multiply nnrat-one 'epsilon) 'epsilon
           normalize-product one-product)
          normalize-affine
          (add-respects
           upper-expectation upper-expectation
           (multiply total 'epsilon) 'epsilon
           (equivalent-reflexive upper-expectation) normalized-product)
          shifted-is-target
          (equivalent-transitive
           shifted-expectation
           (add upper-expectation (multiply total 'epsilon))
           target affine normalize-affine)
          shifted-at-most-target
          (function/app (function/const* 'nnrat/equivalent-to-at-most [])
                        shifted-expectation target shifted-is-target)]
      (function/app
       (function/const* 'nnrat/at-most-transitive [])
       lower-expectation shifted-expectation target
       expectation-ordered shifted-at-most-target)))})

(def action-backup-additive-upper-bound-spec
  {:name 'bellman/nnrat-action-backup-additive-upper-bound
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['left-value (function/arrow 'S nnrat)]
     ['right-value (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['left-pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'left-value 'next-state)
                (add (function/app 'right-value 'next-state) 'epsilon)))]
     ['state 'S]
     ['action 'A]
     ['row-normalized
      (equivalent
       (total-mass 'S 'states
                   (function/app 'transition 'state 'action))
       nnrat-one)]]
    (at-most
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'left-value 'state 'action)
     (add
      (action-backup 'S 'A 'states 'transition 'reward 'discount
                     'right-value 'state 'action)
      (multiply 'discount 'epsilon))))
   :value
   (function/lam
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['left-value (function/arrow 'S nnrat)]
     ['right-value (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['left-pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'left-value 'next-state)
                (add (function/app 'right-value 'next-state) 'epsilon)))]
     ['state 'S]
     ['action 'A]
     ['row-normalized
      (equivalent
       (total-mass 'S 'states
                   (function/app 'transition 'state 'action))
       nnrat-one)]]
    (let [mass (function/app 'transition 'state 'action)
          reward-value (function/app 'reward 'state 'action)
          left-expectation
          (expectation 'S 'states mass 'left-value)
          right-expectation
          (expectation 'S 'states mass 'right-value)
          discounted-left (multiply 'discount left-expectation)
          discounted-right (multiply 'discount right-expectation)
          discounted-epsilon (multiply 'discount 'epsilon)
          discounted-shift
          (multiply 'discount (add right-expectation 'epsilon))
          unfolded-left (add reward-value discounted-left)
          ordered-upper (add reward-value discounted-shift)
          target (add (add reward-value discounted-right)
                      discounted-epsilon)
          expectation-bound
          (function/app
           (function/const*
            'probability/nnrat-expectation-additive-upper-bound-normalized
            [U])
           'S 'states mass 'row-normalized
           'left-value 'right-value 'epsilon 'left-pointwise)
          discounted-bound
          (function/app (function/const* 'nnrat/multiply-monotone [])
                        'discount left-expectation
                        (add right-expectation 'epsilon)
                        expectation-bound)
          reward-bound
          (function/app (function/const* 'nnrat/add-left-monotone [])
                        reward-value discounted-left discounted-shift
                        discounted-bound)
          associate-target
          (function/app (function/const* 'nnrat/add-associative [])
                        reward-value discounted-right discounted-epsilon)
          distribute-discount
          (function/app
           (function/const* 'nnrat/multiply-distributes-add-left [])
           'discount right-expectation 'epsilon)
          collect-discount
          (add-respects
           reward-value reward-value
           (add discounted-right discounted-epsilon) discounted-shift
           (equivalent-reflexive reward-value)
           (equivalent-symmetric
            discounted-shift
            (add discounted-right discounted-epsilon)
            distribute-discount))
          target-is-upper
          (equivalent-transitive
           target
           (add reward-value (add discounted-right discounted-epsilon))
           ordered-upper associate-target collect-discount)]
      (function/app
       (function/const* 'nnrat/at-most-respects-equivalence [])
       (action-backup 'S 'A 'states 'transition 'reward 'discount
                      'left-value 'state 'action)
       unfolded-left
       (add
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'right-value 'state 'action)
        discounted-epsilon)
       ordered-upper
       (equivalent-reflexive unfolded-left)
       target-is-upper
       reward-bound)))})

(def action-backup-additively-contractive-spec
  (let [left-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'left-value 'state 'action)
        right-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'right-value 'state 'action)
        contracted-epsilon (multiply 'discount 'epsilon)
        left-to-right
        (at-most left-backup (add right-backup contracted-epsilon))
        right-to-left
        (at-most right-backup (add left-backup contracted-epsilon))]
    {:name 'bellman/nnrat-action-backup-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['state 'S]
       ['action 'A]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states
                     (function/app 'transition 'state 'action))
         nnrat-one)]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['state 'S]
       ['action 'A]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states
                     (function/app 'transition 'state 'action))
         nnrat-one)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (function/app
        (function/const*
         'bellman/nnrat-action-backup-additive-upper-bound [U V])
        'S 'A 'states 'transition 'reward 'discount
        'left-value 'right-value 'epsilon 'left-pointwise
        'state 'action 'row-normalized)
       (function/app
        (function/const*
         'bellman/nnrat-action-backup-additive-upper-bound [U V])
        'S 'A 'states 'transition 'reward 'discount
        'right-value 'left-value 'epsilon 'right-pointwise
        'state 'action 'row-normalized)))}))

(def optimality-step-additively-contractive-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        contracted-epsilon (multiply 'discount 'epsilon)]
    {:name 'value/nnrat-optimality-step-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'state)))]
       ['normalized
        (rows-normalized 'S 'A 'states 'transition)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (at-most (function/app 'left-value 'state)
                  (add (function/app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (at-most (function/app 'right-value 'state)
                  (add (function/app 'left-value 'state) 'epsilon)))]]
      (function/forall
       [['state 'S]]
       (let [left-step
             (optimality-step 'S 'A 'actions 'fallback backup
                              'left-value 'state)
             right-step
             (optimality-step 'S 'A 'actions 'fallback backup
                              'right-value 'state)]
         (proposition/conjunction
          (at-most left-step (add right-step contracted-epsilon))
          (at-most right-step (add left-step contracted-epsilon))))))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'state)))]
       ['normalized
        (rows-normalized 'S 'A 'states 'transition)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (at-most (function/app 'left-value 'state)
                  (add (function/app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (at-most (function/app 'right-value 'state)
                  (add (function/app 'left-value 'state) 'epsilon)))]]
      (function/lam
       [['state 'S]]
       (let [left-action-pointwise
             (function/lam
              [['action 'A]
               ['member (source-membership V 'A 'actions 'action)]]
              (function/app
               (function/const*
                'bellman/nnrat-action-backup-additive-upper-bound [U V])
               'S 'A 'states 'transition 'reward 'discount
               'left-value 'right-value 'epsilon 'left-pointwise
               'state 'action
               (function/app 'normalized 'state 'action)))
             right-action-pointwise
             (function/lam
              [['action 'A]
               ['member (source-membership V 'A 'actions 'action)]]
              (function/app
               (function/const*
                'bellman/nnrat-action-backup-additive-upper-bound [U V])
               'S 'A 'states 'transition 'reward 'discount
               'right-value 'left-value 'epsilon 'right-pointwise
               'state 'action
               (function/app 'normalized 'state 'action)))]
         (function/app
          (function/const*
           'value/nnrat-optimality-step-additively-nonexpansive [U V])
          'S 'A 'actions 'fallback 'fallback-admissible backup
          'left-value 'right-value contracted-epsilon 'state
          left-action-pointwise right-action-pointwise))))}))

(def contraction-radius-converges-spec
  (let [gamma
        (function/app
         (function/const* 'nnrat/make [])
         (succ 'ap)
         (function/app (function/const* 'algebra/nat-add [])
                       'ap (succ 'gp)))
        radius
        (function/app (function/const* 'value/nnrat-contraction-radius [])
                      gamma 'initial-error)
        general-harmonic-zero
        (function/app (function/const* 'nnrat/general-harmonic [])
                      'ap 'gp zero)]
    {:name 'analysis/nnrat-contraction-radius-converges
     :universes []
     :type
     (function/forall
      [['ap nat]
       ['gp nat]
       ['initial-error nnrat]
       ['initial-bound
        (at-most (function/app radius zero) general-harmonic-zero)]]
      (function/app
       (function/const* 'analysis/rate-null [])
       radius
       (function/lam
        [['k nat]]
        (function/app (function/const* 'nat/multiply [])
                      (succ 'ap) 'k))))
     :value
     (function/lam
      [['ap nat]
       ['gp nat]
       ['initial-error nnrat]
       ['initial-bound
        (at-most (function/app radius zero) general-harmonic-zero)]]
      (function/app
       (function/const* 'analysis/general-contraction-converges [])
       'ap 'gp radius 'initial-bound
       (function/lam
        [['steps nat]]
        (function/app
         (function/const* 'nnrat/at-most-reflexive [])
         (multiply gamma (function/app radius 'steps))))))}))

(def definition-specs
  [total-mass-spec rows-normalized-spec contraction-radius-spec])

(def theorem-specs
  [multiply-distributes-add-left-spec
   expectation-add-constant-spec
   expectation-additive-upper-bound-normalized-spec
   action-backup-additive-upper-bound-spec
   action-backup-additively-contractive-spec
   optimality-step-additively-contractive-spec
   contraction-radius-converges-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Finite Bellman value optimality expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-bellman-value-optimality}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Finite Bellman value optimality declaration was rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (let [base (-> checked-environment
                 monotone/extend-environment
                 optimal/extend-environment
                 map-respects/extend-environment
                 map-scale/extend-environment
                 multiply-commute/extend-environment
                 general-contraction/extend-environment)]
    (reduce add-spec base (concat definition-specs theorem-specs))))

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
