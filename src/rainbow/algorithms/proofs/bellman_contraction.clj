(ns rainbow.algorithms.proofs.bellman-contraction
  "Finite fixed-policy Bellman contraction over exact natural numerators."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
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
(def two (function/app successor one))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- nil-list [element]
  (function/app (function/const* 'data/nil [data-level]) element))

(defn- cons-list [element head tail]
  (function/app (function/const* 'data/cons [data-level])
                element head tail))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [U])
                element source value))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nat-map-sum [U])
                element mapping source))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- expectation [element source mass value]
  (function/app
   (function/const* 'probability/expectation-numerator [U])
   element source mass value))

(defn- weight-total [element source mass]
  (function/app (function/const* 'probability/weight-total [U])
                element source mass))

(defn- row-total [element source transition state]
  (function/app (function/const* 'markov/row-total [U])
                element source transition state))

(defn- rows-normalized [element scale source transition]
  (function/app (function/const* 'markov/rows-normalized-at [U])
                element scale source transition))

(defn- bellman
  [element scale source transition reward discount value state]
  (function/app
   (function/const* 'bellman/fixed-policy-numerator [U])
   element scale source transition reward discount value state))

(defn- finite-sup-distance [element source left right]
  (function/app (function/const* 'metric/finite-sup-distance [U])
                element source left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(def list-map-sum-distance-bound-by-on-spec
  (let [left-sum (fn [source] (map-sum 'A 'left source))
        right-sum (fn [source] (map-sum 'A 'right source))
        bound-sum (fn [source] (map-sum 'A 'bound source))
        pointwise-type
        (fn [source]
          (function/forall
           [['value 'A] ['member (membership 'A source 'value)]]
           (at-most
            (distance (function/app 'left 'value)
                      (function/app 'right 'value))
            (function/app 'bound 'value))))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (function/arrow
          (pointwise-type 'source)
          (at-most
           (distance (left-sum 'source) (right-sum 'source))
           (bound-sum 'source))))]
    {:name 'list/nat-map-sum-distance-bound-by-on
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['bound (function/arrow 'A nat)]
       ['source (list-of 'A)]
       ['pointwise (pointwise-type 'source)]]
      (at-most
       (distance (left-sum 'source) (right-sum 'source))
       (bound-sum 'source)))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['bound (function/arrow 'A nat)]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['ignored (pointwise-type (nil-list 'A))]]
        (function/app (function/const* 'nat/at-most-reflexive []) zero))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['pointwise (pointwise-type (cons-list 'A 'head 'tail))]]
        (let [left-head (function/app 'left 'head)
              right-head (function/app 'right 'head)
              left-tail (left-sum 'tail)
              right-tail (right-sum 'tail)
              left-total (add left-head left-tail)
              bridge (add right-head left-tail)
              right-total (add right-head right-tail)
              head-distance (distance left-head right-head)
              tail-distance (distance left-tail right-tail)
              triangle-upper
              (add (distance left-total bridge)
                   (distance bridge right-total))
              reduced-upper (add head-distance tail-distance)
              reduce-head
              (congruent
               (function/lam
                [['value nat]]
                (add 'value (distance bridge right-total)))
               (distance left-total bridge) head-distance
               (function/app
                (function/const* 'nat/distance-add-right [])
                left-head left-tail right-head))
              reduce-tail
              (congruent
               (function/lam [['value nat]] (add head-distance 'value))
               (distance bridge right-total) tail-distance
               (function/app
                (function/const* 'nat/distance-add-left [])
                right-head left-tail right-tail))
              reduced-middle
              (add head-distance (distance bridge right-total))
              reduce-upper
              (transitive triangle-upper reduced-middle reduced-upper
                          reduce-head reduce-tail)
              triangle-reduced
              (function/app
               (function/const* 'nat/at-most-rewrite-right [])
               (distance left-total right-total)
               triangle-upper reduced-upper reduce-upper
               (function/app
                (function/const* 'nat/distance-triangle [])
                left-total bridge right-total))
              head-member
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (function/equality data-level 'A 'head 'head)
               (membership 'A 'tail 'head)
               (function/app
                (function/const* 'equality/reflexive [data-level])
                'A 'head))
              tail-pointwise
              (function/lam
               [['value 'A] ['member (membership 'A 'tail 'value)]]
               (function/app
                'pointwise 'value
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 (function/equality data-level 'A 'value 'head)
                 (membership 'A 'tail 'value) 'member)))
              component-bound
              (function/app
               (function/const* 'nat/add-monotone [])
               head-distance (function/app 'bound 'head)
               tail-distance (bound-sum 'tail)
               (function/app 'pointwise 'head head-member)
               (function/app 'induction-hypothesis tail-pointwise))]
          (function/app
           (function/const* 'nat/at-most-transitive [])
           (distance left-total right-total) reduced-upper
           (add (function/app 'bound 'head) (bound-sum 'tail))
           triangle-reduced component-bound)))
       'source))}))

(def expectation-distance-bound-on-spec
  (let [left-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'left 'state)
                   (function/app 'mass 'state)))
        right-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'right 'state)
                   (function/app 'mass 'state)))
        bound-weighted
        (function/lam
         [['state 'A]]
         (multiply (function/app 'mass 'state) 'epsilon))
        source-list (enumeration 'A 'source)
        bound-sum (map-sum 'A bound-weighted source-list)
        finish (multiply (weight-total 'A 'source 'mass) 'epsilon)]
    {:name 'probability/expectation-distance-bound-on
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (at-most
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))
          'epsilon))]]
      (at-most
       (distance (expectation 'A 'source 'mass 'left)
                 (expectation 'A 'source 'mass 'right))
       finish))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nat)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['epsilon nat]
       ['pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (at-most
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))
          'epsilon))]]
      (let [weighted-pointwise
            (function/lam
             [['state 'A]
              ['member (membership 'A source-list 'state)]]
             (let [left-value (function/app 'left 'state)
                   right-value (function/app 'right 'state)
                   state-mass (function/app 'mass 'state)
                   value-distance (distance left-value right-value)
                   weighted-distance
                   (distance (multiply left-value state-mass)
                             (multiply right-value state-mass))
                   product-distance (multiply value-distance state-mass)
                   product-bound (multiply 'epsilon state-mass)
                   finish-bound (multiply state-mass 'epsilon)
                   scale-bound
                   (function/app
                    (function/const* 'nat/multiply-right-monotone [])
                    state-mass value-distance 'epsilon
                    (function/app 'pointwise 'state 'member))
                   scale-bound
                   (function/app
                    (function/const* 'nat/at-most-rewrite-right [])
                    product-distance product-bound finish-bound
                    (function/app
                     (function/const* 'nat/multiply-commutative [])
                     'epsilon state-mass)
                    scale-bound)]
               (function/app
                (function/const* 'nat/at-most-rewrite-left [])
                weighted-distance product-distance finish-bound
                (function/app
                 (function/const* 'nat/distance-multiply-right [])
                 left-value right-value state-mass)
                scale-bound)))
            sum-bound
            (function/app
             (function/const*
              'list/nat-map-sum-distance-bound-by-on [U])
             'A left-weighted right-weighted bound-weighted
             source-list weighted-pointwise)
            sum-equality
            (function/app
             (function/const* 'list/nat-map-sum-multiply-right [U])
             'A 'mass 'epsilon source-list)]
        (function/app
         (function/const* 'nat/at-most-rewrite-right [])
         (distance (expectation 'A 'source 'mass 'left)
                   (expectation 'A 'source 'mass 'right))
         bound-sum finish sum-equality sum-bound)))}))

(def fixed-policy-pointwise-contraction-spec
  (let [left-expectation
        (expectation 'A 'source (function/app 'transition 'state) 'left)
        right-expectation
        (expectation 'A 'source (function/app 'transition 'state) 'right)
        expectation-distance (distance left-expectation right-expectation)
        row-mass (row-total 'A 'source 'transition 'state)
        expectation-bound (multiply row-mass 'epsilon)
        normalized-bound (multiply 'scale 'epsilon)
        finish (multiply 'discount normalized-bound)
        reward-term
        (multiply (function/app 'reward 'state)
                  (multiply 'scale 'scale))
        left-continuation (multiply 'discount left-expectation)
        right-continuation (multiply 'discount right-expectation)
        left-output
        (bellman 'A 'scale 'source 'transition 'reward
                 'discount 'left 'state)
        right-output
        (bellman 'A 'scale 'source 'transition 'reward
                 'discount 'right 'state)]
    {:name 'bellman/fixed-policy-pointwise-contraction
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)] ['epsilon nat]
       ['normalized (rows-normalized 'A 'scale 'source 'transition)]
       ['pointwise
        (function/forall
         [['next 'A]
          ['member (source-membership 'A 'source 'next)]]
         (at-most
          (distance (function/app 'left 'next)
                    (function/app 'right 'next))
          'epsilon))]
       ['state 'A]]
      (at-most (distance left-output right-output) finish))
     :value
     (function/lam
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)] ['epsilon nat]
       ['normalized (rows-normalized 'A 'scale 'source 'transition)]
       ['pointwise
        (function/forall
         [['next 'A]
          ['member (source-membership 'A 'source 'next)]]
         (at-most
          (distance (function/app 'left 'next)
                    (function/app 'right 'next))
          'epsilon))]
       ['state 'A]]
      (let [expectation-ordered
            (function/app
             (function/const* 'probability/expectation-distance-bound-on [U])
             'A 'source (function/app 'transition 'state)
             'left 'right 'epsilon 'pointwise)
            scaled-ordered
            (function/app
             (function/const* 'nat/multiply-left-monotone [])
             'discount expectation-distance expectation-bound
             expectation-ordered)
            scaled-row-bound (multiply 'discount expectation-bound)
            replace-row
            (congruent
             (function/lam
              [['total nat]]
              (multiply 'discount (multiply 'total 'epsilon)))
             row-mass 'scale (function/app 'normalized 'state))
            scaled-normalized
            (function/app
             (function/const* 'nat/at-most-rewrite-right [])
             (multiply 'discount expectation-distance)
             scaled-row-bound finish replace-row scaled-ordered)
            output-distance (distance left-output right-output)
            continuation-distance
            (distance left-continuation right-continuation)
            scaled-distance (multiply 'discount expectation-distance)
            remove-reward
            (function/app (function/const* 'nat/distance-add-left [])
                          reward-term left-continuation right-continuation)
            expose-scale
            (function/app (function/const* 'nat/distance-multiply-left [])
                          'discount left-expectation right-expectation)
            reduce-output
            (transitive output-distance continuation-distance scaled-distance
                        remove-reward expose-scale)]
        (function/app
         (function/const* 'nat/at-most-rewrite-left [])
         output-distance scaled-distance finish
         reduce-output scaled-normalized)))}))

(def fixed-policy-sup-contraction-spec
  (let [left-bellman
        (function/lam
         [['state 'A]]
         (bellman 'A 'scale 'source 'transition 'reward
                  'discount 'left 'state))
        right-bellman
        (function/lam
         [['state 'A]]
         (bellman 'A 'scale 'source 'transition 'reward
                  'discount 'right 'state))
        epsilon (finite-sup-distance 'A 'source 'left 'right)
        finish (multiply 'discount (multiply 'scale epsilon))
        output-mapping
        (function/lam
         [['state 'A]]
         (distance (function/app left-bellman 'state)
                   (function/app right-bellman 'state)))]
    {:name 'bellman/fixed-policy-sup-contraction
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['normalized (rows-normalized 'A 'scale 'source 'transition)]]
      (at-most
       (finite-sup-distance 'A 'source left-bellman right-bellman)
       finish))
     :value
     (function/lam
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['normalized (rows-normalized 'A 'scale 'source 'transition)]]
      (function/app
       (function/const* 'list/nat-map-max-bounded [U])
       'A output-mapping finish (enumeration 'A 'source)
       (function/lam
        [['state 'A]
         ['member (membership 'A (enumeration 'A 'source) 'state)]]
        (function/app
         (function/const* 'bellman/fixed-policy-pointwise-contraction [U])
         'A 'scale 'source 'transition 'reward 'discount
         'left 'right epsilon 'normalized
         (function/lam
          [['next 'A]
           ['next-member (source-membership 'A 'source 'next)]]
          (function/app
           (function/const* 'metric/finite-sup-upper-bound [U])
           'A 'source 'left 'right 'next 'next-member))
         'state))))}))

(def two-state-contraction-example-spec
  (let [bellman-zero
        (fn [element scale source transition reward discount value state]
          (function/app
           (function/const* 'bellman/fixed-policy-numerator [zero-level])
           element scale source transition reward discount value state))
        finite-sup-zero
        (fn [element source left right]
          (function/app
           (function/const* 'metric/finite-sup-distance [zero-level])
           element source left right))
        source (function/const* 'or-example/two-state-space [])
        transition (function/const* 'or-example/uniform-transition [])
        reward (function/const* 'or-example/identity-value [])
        left (function/const* 'or-example/identity-value [])
        right (function/lam [['state nat]] zero)
        left-bellman
        (function/lam
         [['state nat]]
         (bellman-zero nat two source transition reward one left 'state))
        right-bellman
        (function/lam
         [['state nat]]
         (bellman-zero nat two source transition reward one right 'state))]
    {:name 'bellman/two-state-contraction-example
     :universes []
     :type
     (at-most
      (finite-sup-zero nat source left-bellman right-bellman)
      two)
     :value
     (function/app
      (function/const* 'bellman/fixed-policy-sup-contraction [zero-level])
      nat two source transition reward one left right
      (function/const* 'markov/two-state-rows-normalized []))}))

(def theorem-specs
  [list-map-sum-distance-bound-by-on-spec
   expectation-distance-bound-on-spec
   fixed-policy-pointwise-contraction-spec
   fixed-policy-sup-contraction-spec
   two-state-contraction-example-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Bellman contraction expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-bellman-contraction}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Bellman contraction theorem was rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.bellman-contraction))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
