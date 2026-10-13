(ns rainbow.math.finite.metric
  "Constructive maximum folds and finite sup-distance over exact finite data."
  (:require [rainbow.elaborate :as elaborate]
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

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- recursive-max [left right]
  (function/app (function/const* 'nat/recursive-max []) left right))

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

(defn- map-max [element mapping source]
  (function/app (function/const* 'list/nat-map-max [U])
                element mapping source))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- finite-sup-distance [element source left right]
  (function/app (function/const* 'metric/finite-sup-distance [U])
                element source left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- nat-equality [left right]
  (equality nat left right))

(defn- reflexive [carrier value]
  (function/app (function/const* 'equality/reflexive [type-level])
                carrier value))

(defn- transitive [carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                carrier left middle right first second))

(defn- symmetric [carrier left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                carrier left right same))

(defn- congruent
  [source-level target-level source target mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [source-level target-level])
   source target mapping left right same))

(defn- zero-at-most [right]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['extra nat]]
                 (nat-equality (add zero 'extra) right))
   right
   (reflexive nat right)))

(def recursive-max-spec
  {:name 'nat/recursive-max
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] (function/arrow nat nat))
     (function/lam [['right nat]] 'right)
     (function/lam
      [['left-previous nat]
       ['previous-max (function/arrow nat nat)]]
      (function/lam
       [['right nat]]
       (function/app
        (function/const* 'data/Nat.rec [type-level])
        (function/lam [['ignored nat]] nat)
        (succ 'left-previous)
        (function/lam
         [['right-previous nat] ['ignored nat]]
         (succ (function/app 'previous-max 'right-previous)))
        'right)))
     'left))})

(def list-map-max-spec
  {:name 'list/nat-map-max
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A nat)]]
    (function/arrow (list-of 'A) nat))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A nat)]
     ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] nat)
     zero
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-max nat]]
      (recursive-max (function/app 'mapping 'head) 'tail-max))
     'source))})

(def finite-sup-distance-spec
  {:name 'metric/finite-sup-distance
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]]
    nat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]]
    (map-max
     'A
     (function/lam
      [['state 'A]]
      (distance (function/app 'left 'state)
                (function/app 'right 'state)))
     (enumeration 'A 'source)))})

(def recursive-max-left-bound-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (at-most 'left (recursive-max 'left 'right))))]
    {:name 'nat/recursive-max-left-bound
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (at-most 'left (recursive-max 'left 'right)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam [['right nat]] (zero-at-most 'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (at-most (succ 'left-previous)
                   (recursive-max (succ 'left-previous) 'candidate)))
         (function/app (function/const* 'nat/at-most-reflexive [])
                       (succ 'left-previous))
         (function/lam
          [['right-previous nat]
           ['ignored
            (at-most (succ 'left-previous)
                     (recursive-max (succ 'left-previous)
                                    'right-previous))]]
          (function/app
           (function/const* 'nat/add-left-monotone [])
           one 'left-previous
           (recursive-max 'left-previous 'right-previous)
           (function/app 'induction-hypothesis 'right-previous)))
         'right))
       'left))}))

(def recursive-max-right-bound-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (at-most 'right (recursive-max 'left 'right))))]
    {:name 'nat/recursive-max-right-bound
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (at-most 'right (recursive-max 'left 'right)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app (function/const* 'nat/at-most-reflexive []) 'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (at-most 'candidate
                   (recursive-max (succ 'left-previous) 'candidate)))
         (zero-at-most (succ 'left-previous))
         (function/lam
          [['right-previous nat]
           ['ignored
            (at-most 'right-previous
                     (recursive-max (succ 'left-previous)
                                    'right-previous))]]
          (function/app
           (function/const* 'nat/add-left-monotone [])
           one 'right-previous
           (recursive-max 'left-previous 'right-previous)
           (function/app 'induction-hypothesis 'right-previous)))
         'right))
       'left))}))

(def recursive-max-commutative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (nat-equality (recursive-max 'left 'right)
                        (recursive-max 'right 'left))))]
    {:name 'nat/recursive-max-commutative
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (nat-equality (recursive-max 'left 'right)
                    (recursive-max 'right 'left)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (nat-equality (recursive-max zero 'candidate)
                        (recursive-max 'candidate zero)))
         (reflexive nat zero)
         (function/lam
          [['previous nat]
           ['ignored
            (nat-equality (recursive-max zero 'previous)
                          (recursive-max 'previous zero))]]
          (reflexive nat (succ 'previous)))
         'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (nat-equality
           (recursive-max (succ 'left-previous) 'candidate)
           (recursive-max 'candidate (succ 'left-previous))))
         (reflexive nat (succ 'left-previous))
         (function/lam
          [['right-previous nat]
           ['ignored
            (nat-equality
             (recursive-max (succ 'left-previous) 'right-previous)
             (recursive-max 'right-previous (succ 'left-previous)))]]
          (congruent
           type-level type-level nat nat
           (function/lam [['value nat]] (succ 'value))
           (recursive-max 'left-previous 'right-previous)
           (recursive-max 'right-previous 'left-previous)
           (function/app 'induction-hypothesis 'right-previous)))
         'right))
       'left))}))

(def recursive-max-is-side-spec
  (let [side
        (fn [left right]
          (proposition/disjunction
           (nat-equality (recursive-max left right) left)
           (nat-equality (recursive-max left right) right)))
        motive
        (function/lam [['left nat]]
                      (function/forall [['right nat]] (side 'left 'right)))]
    {:name 'nat/recursive-max-is-left-or-right
     :universes []
     :type
     (function/forall [['left nat] ['right nat]] (side 'left 'right))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app (function/const* 'proposition/right-disjunct [])
                      (nat-equality (recursive-max zero 'right) zero)
                      (nat-equality (recursive-max zero 'right) 'right)
                      (reflexive nat 'right)))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (side (succ 'left-previous) 'candidate))
         (function/app
          (function/const* 'proposition/left-disjunct [])
          (nat-equality (recursive-max (succ 'left-previous) zero)
                        (succ 'left-previous))
          (nat-equality (recursive-max (succ 'left-previous) zero) zero)
          (reflexive nat (succ 'left-previous)))
         (function/lam
          [['right-previous nat]
           ['ignored (side (succ 'left-previous) 'right-previous)]]
          (let [previous-side (side 'left-previous 'right-previous)
                current-side (side (succ 'left-previous)
                                   (succ 'right-previous))
                lift
                (fn [value]
                  (congruent
                   type-level type-level nat nat
                   (function/lam [['candidate nat]] (succ 'candidate))
                   (recursive-max 'left-previous 'right-previous)
                   value
                   (if (= value 'left-previous)
                     'same-left
                     'same-right)))]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             (nat-equality (recursive-max 'left-previous 'right-previous)
                           'left-previous)
             (nat-equality (recursive-max 'left-previous 'right-previous)
                           'right-previous)
             current-side
             (function/app 'induction-hypothesis 'right-previous)
             (function/lam
              [['same-left
                (nat-equality
                 (recursive-max 'left-previous 'right-previous)
                 'left-previous)]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (nat-equality
                (recursive-max (succ 'left-previous) (succ 'right-previous))
                (succ 'left-previous))
               (nat-equality
                (recursive-max (succ 'left-previous) (succ 'right-previous))
                (succ 'right-previous))
               (lift 'left-previous)))
             (function/lam
              [['same-right
                (nat-equality
                 (recursive-max 'left-previous 'right-previous)
                 'right-previous)]]
              (function/app
               (function/const* 'proposition/right-disjunct [])
               (nat-equality
                (recursive-max (succ 'left-previous) (succ 'right-previous))
                (succ 'left-previous))
               (nat-equality
                (recursive-max (succ 'left-previous) (succ 'right-previous))
                (succ 'right-previous))
               (lift 'right-previous))))))
         'right))
       'left))}))

(def recursive-max-least-upper-bound-spec
  {:name 'nat/recursive-max-least-upper-bound
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat] ['upper nat]
     ['left-bound (at-most 'left 'upper)]
     ['right-bound (at-most 'right 'upper)]]
    (at-most (recursive-max 'left 'right) 'upper))
   :value
   (function/lam
    [['left nat] ['right nat] ['upper nat]
     ['left-bound (at-most 'left 'upper)]
     ['right-bound (at-most 'right 'upper)]]
    (function/app
     (function/const* 'proposition/use-disjunction [])
     (nat-equality (recursive-max 'left 'right) 'left)
     (nat-equality (recursive-max 'left 'right) 'right)
     (at-most (recursive-max 'left 'right) 'upper)
     (function/app (function/const* 'nat/recursive-max-is-left-or-right [])
                   'left 'right)
     (function/lam
      [['same-left (nat-equality (recursive-max 'left 'right) 'left)]]
      (function/app (function/const* 'nat/at-most-rewrite-left [])
                    (recursive-max 'left 'right) 'left 'upper
                    'same-left 'left-bound))
     (function/lam
      [['same-right (nat-equality (recursive-max 'left 'right) 'right)]]
      (function/app (function/const* 'nat/at-most-rewrite-left [])
                    (recursive-max 'left 'right) 'right 'upper
                    'same-right 'right-bound))))})

(def list-map-max-upper-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (at-most (function/app 'mapping 'value)
                   (map-max 'A 'mapping 'source))))]
    {:name 'list/nat-map-max-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A nat)]
       ['source (list-of 'A)] ['value 'A]
       ['member (membership 'A 'source 'value)]]
      (at-most (function/app 'mapping 'value)
               (map-max 'A 'mapping 'source)))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A nat)]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['value 'A]
         ['impossible (membership 'A (nil-list 'A) 'value)]]
        (function/app (function/const* 'proposition/explode [])
                      (at-most (function/app 'mapping 'value) zero)
                      'impossible))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value 'A]
         ['member
          (membership 'A (cons-list 'A 'head 'tail) 'value)]]
        (let [head-case (function/equality data-level 'A 'value 'head)
              tail-case (membership 'A 'tail 'value)
              target
              (at-most
               (function/app 'mapping 'value)
               (recursive-max (function/app 'mapping 'head)
                              (map-max 'A 'mapping 'tail)))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (function/app
             (function/const* 'nat/at-most-rewrite-left [])
             (function/app 'mapping 'value)
             (function/app 'mapping 'head)
             (recursive-max (function/app 'mapping 'head)
                            (map-max 'A 'mapping 'tail))
             (congruent data-level type-level 'A nat 'mapping
                        'value 'head 'same)
             (function/app
              (function/const* 'nat/recursive-max-left-bound [])
              (function/app 'mapping 'head)
              (map-max 'A 'mapping 'tail))))
           (function/lam
            [['tail-member tail-case]]
            (function/app
             (function/const* 'nat/at-most-transitive [])
             (function/app 'mapping 'value)
             (map-max 'A 'mapping 'tail)
             (recursive-max (function/app 'mapping 'head)
                            (map-max 'A 'mapping 'tail))
             (function/app 'induction-hypothesis 'value 'tail-member)
             (function/app
              (function/const* 'nat/recursive-max-right-bound [])
              (function/app 'mapping 'head)
              (map-max 'A 'mapping 'tail)))))))
       'source))}))

(def list-map-max-bounded-spec
  (let [bounded
        (fn [source]
          (function/forall
           [['value 'A] ['member (membership 'A source 'value)]]
           (at-most (function/app 'mapping 'value) 'upper)))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (function/arrow (bounded 'source)
                         (at-most (map-max 'A 'mapping 'source) 'upper)))]
    {:name 'list/nat-map-max-bounded
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['mapping (function/arrow 'A nat)]
       ['upper nat] ['source (list-of 'A)]
       ['pointwise (bounded 'source)]]
      (at-most (map-max 'A 'mapping 'source) 'upper))
     :value
     (function/lam
      [['A type-u] ['mapping (function/arrow 'A nat)] ['upper nat]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['ignored (bounded (nil-list 'A))]]
        (zero-at-most 'upper))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['pointwise (bounded (cons-list 'A 'head 'tail))]]
        (let [head-case (function/equality data-level 'A 'head 'head)
              tail-bounded (bounded 'tail)
              head-member
              (function/app
               (function/const* 'proposition/left-disjunct [])
               head-case (membership 'A 'tail 'head)
               (function/app
                (function/const* 'equality/reflexive [data-level])
                'A 'head))
              tail-pointwise
              (function/lam
               [['value 'A] ['tail-member (membership 'A 'tail 'value)]]
               (function/app
                'pointwise 'value
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 (function/equality data-level 'A 'value 'head)
                 (membership 'A 'tail 'value) 'tail-member)))]
          (function/app
           (function/const* 'nat/recursive-max-least-upper-bound [])
           (function/app 'mapping 'head) (map-max 'A 'mapping 'tail)
           'upper
           (function/app 'pointwise 'head head-member)
           (function/app 'induction-hypothesis tail-pointwise))))
       'source))}))

(def list-map-max-congruent-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (nat-equality (map-max 'A 'left 'source)
                       (map-max 'A 'right 'source)))]
    {:name 'list/nat-map-max-congruent
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['pointwise
        (function/forall
         [['value 'A]]
         (nat-equality (function/app 'left 'value)
                       (function/app 'right 'value)))]
       ['source (list-of 'A)]]
      (nat-equality (map-max 'A 'left 'source)
                    (map-max 'A 'right 'source)))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['pointwise
        (function/forall
         [['value 'A]]
         (nat-equality (function/app 'left 'value)
                       (function/app 'right 'value)))]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (reflexive nat zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [left-head (function/app 'left 'head)
              right-head (function/app 'right 'head)
              left-tail (map-max 'A 'left 'tail)
              right-tail (map-max 'A 'right 'tail)
              start (recursive-max left-head left-tail)
              middle (recursive-max right-head left-tail)
              finish (recursive-max right-head right-tail)]
          (transitive
           nat start middle finish
           (congruent type-level type-level nat nat
                      (function/lam [['value nat]]
                                    (recursive-max 'value left-tail))
                      left-head right-head
                      (function/app 'pointwise 'head))
           (congruent type-level type-level nat nat
                      (function/lam [['value nat]]
                                    (recursive-max right-head 'value))
                      left-tail right-tail 'induction-hypothesis))))
       'source))}))

(def finite-sup-upper-bound-spec
  (let [pointwise
        (function/lam
         [['state 'A]]
         (distance (function/app 'left 'state)
                   (function/app 'right 'state)))]
    {:name 'metric/finite-sup-upper-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (at-most
       (distance (function/app 'left 'state)
                 (function/app 'right 'state))
       (finite-sup-distance 'A 'source 'left 'right)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['state 'A]
       ['member (source-membership 'A 'source 'state)]]
      (function/app
       (function/const* 'list/nat-map-max-upper-bound [U])
       'A pointwise (enumeration 'A 'source) 'state 'member))}))

(def finite-sup-symmetric-spec
  {:name 'metric/finite-sup-symmetric
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]]
    (nat-equality
     (finite-sup-distance 'A 'source 'left 'right)
     (finite-sup-distance 'A 'source 'right 'left)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]]
    (function/app
     (function/const* 'list/nat-map-max-congruent [U])
     'A
     (function/lam
      [['state 'A]]
      (distance (function/app 'left 'state)
                (function/app 'right 'state)))
     (function/lam
      [['state 'A]]
      (distance (function/app 'right 'state)
                (function/app 'left 'state)))
     (function/lam
      [['state 'A]]
      (function/app (function/const* 'nat/distance-commutative [])
                    (function/app 'left 'state)
                    (function/app 'right 'state)))
     (enumeration 'A 'source)))})

(def finite-sup-triangle-spec
  (let [left-middle
        (finite-sup-distance 'A 'source 'left 'middle)
        middle-right
        (finite-sup-distance 'A 'source 'middle 'right)
        upper (add left-middle middle-right)
        left-right-mapping
        (function/lam
         [['state 'A]]
         (distance (function/app 'left 'state)
                   (function/app 'right 'state)))]
    {:name 'metric/finite-sup-triangle
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['middle (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (at-most
       (finite-sup-distance 'A 'source 'left 'right)
       upper))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['middle (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (function/app
       (function/const* 'list/nat-map-max-bounded [U])
       'A left-right-mapping upper (enumeration 'A 'source)
       (function/lam
        [['state 'A]
         ['member (membership 'A (enumeration 'A 'source) 'state)]]
        (let [left-value (function/app 'left 'state)
              middle-value (function/app 'middle 'state)
              right-value (function/app 'right 'state)
              direct (distance left-value right-value)
              through
              (add (distance left-value middle-value)
                   (distance middle-value right-value))
              components
              (function/app
               (function/const* 'nat/add-monotone [])
               (distance left-value middle-value) left-middle
               (distance middle-value right-value) middle-right
               (function/app
                (function/const* 'metric/finite-sup-upper-bound [U])
                'A 'source 'left 'middle 'state 'member)
               (function/app
                (function/const* 'metric/finite-sup-upper-bound [U])
                'A 'source 'middle 'right 'state 'member))]
          (function/app
           (function/const* 'nat/at-most-transitive [])
           direct through upper
           (function/app (function/const* 'nat/distance-triangle [])
                         left-value middle-value right-value)
           components)))))}))

(def definition-specs
  [recursive-max-spec list-map-max-spec finite-sup-distance-spec])

(def theorem-specs
  [recursive-max-left-bound-spec recursive-max-right-bound-spec
   recursive-max-commutative-spec recursive-max-is-side-spec
   recursive-max-least-upper-bound-spec
   list-map-max-upper-bound-spec list-map-max-bounded-spec
   list-map-max-congruent-spec
   finite-sup-upper-bound-spec finite-sup-symmetric-spec
   finite-sup-triangle-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite metric expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-sup-metric}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite metric declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      extend-definitions
      extend-theorems))

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
