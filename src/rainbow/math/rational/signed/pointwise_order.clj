(ns rainbow.math.rational.signed.pointwise-order
  "Pointwise order over the indices a problem actually has.

  The parametric LP theorems quantify their feasibility hypotheses over the whole
  index TYPE -- `forall i : A, ...`. That is the right statement for a theorem
  and the wrong one for an instance. A real program has data for the rows in its
  row list and for nothing else, so on an index type like `data/Nat` the
  hypothesis is not merely inconvenient to discharge, it is FALSE: there is no
  eighth constraint to satisfy. Only a finite index type such as `data/Bool`
  escapes that, which caps a checker at instances whose size was fixed when the
  theorem was written.

  `signed/all-at-most` fixes the quantifier to the list:

      all-at-most f g nil        = truth
      all-at-most f g (h :: t)   = (f h <= g h) AND all-at-most f g t

  and `signed/map-sum-monotone-on` is the monotonicity a finite sum actually
  needs -- termwise domination ON THE SUMMED INDICES lifts to the sum. The
  existing `signed/map-sum-monotone` is the special case where domination happens
  to hold everywhere.

  For an instance of any size the hypothesis is then built by folding one decided
  comparison per row, which a generator emits in a loop. Nothing here is
  quadratic in the instance and nothing is fixed at theorem-writing time.

  Native and axiom-free on D63; chains the signed finite-sum order laws."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.list-sum :as sum]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- cons-of [element head tail]
  (app (function/const* 'data/cons [data-level]) element head tail))
(defn- nil-of [element]
  (app (function/const* 'data/nil [data-level]) element))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))
(defn- all-at-most [A f g xs]
  (app (function/const* 'signed/all-at-most [U]) A f g xs))

(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))
(defn- truth [] (function/const* 'proposition/truth []))
(defn- trivial [] (function/const* 'proposition/trivial []))

(defn- signed-at-most-reflexive [v]
  (app (function/const* 'signed/at-most-reflexive []) v))
(defn- signed-add-monotone [a ah b bh ha hb]
  (app (function/const* 'signed/add-monotone []) a ah b bh ha hb))

(def function-type (function/arrow 'A signed))

;; ---- the list-quantified pointwise order ------------------------------------

(def all-at-most-spec
  {:name 'signed/all-at-most :kind :definition :universes ['u]
   :transparency :reducible
   :type (function/forall
          [['A type-u] ['f function-type] ['g function-type]]
          (function/arrow (list-of 'A) 'Prop))
   :value
   (function/lam
    [['A type-u] ['f function-type] ['g function-type] ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level type-level])
         'A
         (function/lam [['ignored (list-of 'A)]] 'Prop)
         (truth)
         (function/lam [['head 'A] ['tail (list-of 'A)] ['ih 'Prop]]
                       (conjunction (sle (app 'f 'head) (app 'g 'head)) 'ih))
         'xs))})

(def all-at-most-empty-spec
  {:name 'signed/all-at-most-empty :universes ['u]
   :type (function/forall
          [['A type-u] ['f function-type] ['g function-type]]
          (all-at-most 'A 'f 'g (nil-of 'A)))
   :value (function/lam
           [['A type-u] ['f function-type] ['g function-type]]
           (trivial))})

(def all-at-most-cons-spec
  {:name 'signed/all-at-most-cons :universes ['u]
   :type (function/forall
          [['A type-u] ['f function-type] ['g function-type]
           ['head 'A] ['tail (list-of 'A)]
           ['here (sle (app 'f 'head) (app 'g 'head))]
           ['rest (all-at-most 'A 'f 'g 'tail)]]
          (all-at-most 'A 'f 'g (cons-of 'A 'head 'tail)))
   :value
   (function/lam
    [['A type-u] ['f function-type] ['g function-type]
     ['head 'A] ['tail (list-of 'A)]
     ['here (sle (app 'f 'head) (app 'g 'head))]
     ['rest (all-at-most 'A 'f 'g 'tail)]]
    (conjoin (sle (app 'f 'head) (app 'g 'head))
             (all-at-most 'A 'f 'g 'tail)
             'here 'rest))})

;; Map a BINARY pointwise implication along the list. Instance hypotheses arrive
;; list-quantified, so a per-index lemma taking two facts -- dual feasibility and
;; nonnegativity, say -- cannot be applied at an arbitrary index; it has to be
;; carried across exactly the listed ones.
(def all-at-most-combine-spec
  {:name 'signed/all-at-most-combine :universes ['u]
   :type (function/forall
          [['A type-u]
           ['f function-type] ['g function-type]
           ['p function-type] ['q function-type]
           ['r function-type] ['s function-type]
           ['xs (list-of 'A)]
           ['step (function/forall
                   [['x 'A]
                    ['first (sle (app 'f 'x) (app 'g 'x))]
                    ['second (sle (app 'p 'x) (app 'q 'x))]]
                   (sle (app 'r 'x) (app 's 'x)))]
           ['first (all-at-most 'A 'f 'g 'xs)]
           ['second (all-at-most 'A 'p 'q 'xs)]]
          (all-at-most 'A 'r 's 'xs))
   :value
   (function/lam
    [['A type-u]
     ['f function-type] ['g function-type]
     ['p function-type] ['q function-type]
     ['r function-type] ['s function-type]
     ['xs (list-of 'A)]
     ['step (function/forall
             [['x 'A]
              ['first (sle (app 'f 'x) (app 'g 'x))]
              ['second (sle (app 'p 'x) (app 'q 'x))]]
             (sle (app 'r 'x) (app 's 'x)))]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam
          [['ys (list-of 'A)]]
          (function/forall
           [['first (all-at-most 'A 'f 'g 'ys)]
            ['second (all-at-most 'A 'p 'q 'ys)]]
           (all-at-most 'A 'r 's 'ys)))
         (function/lam
          [['first (all-at-most 'A 'f 'g (nil-of 'A))]
           ['second (all-at-most 'A 'p 'q (nil-of 'A))]]
          (trivial))
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (function/forall
                 [['first (all-at-most 'A 'f 'g 'tail)]
                  ['second (all-at-most 'A 'p 'q 'tail)]]
                 (all-at-most 'A 'r 's 'tail))]
           ['first (all-at-most 'A 'f 'g (cons-of 'A 'head 'tail))]
           ['second (all-at-most 'A 'p 'q (cons-of 'A 'head 'tail))]]
          (let [here-f (sle (app 'f 'head) (app 'g 'head))
                rest-f (all-at-most 'A 'f 'g 'tail)
                here-p (sle (app 'p 'head) (app 'q 'head))
                rest-p (all-at-most 'A 'p 'q 'tail)]
            (conjoin
             (sle (app 'r 'head) (app 's 'head))
             (all-at-most 'A 'r 's 'tail)
             (app 'step 'head
                  (prop-left here-f rest-f 'first)
                  (prop-left here-p rest-p 'second))
             (app 'ih
                  (prop-right here-f rest-f 'first)
                  (prop-right here-p rest-p 'second)))))
         'xs))})

;; ---- the monotonicity a finite sum actually needs ---------------------------

(def map-sum-monotone-on-spec
  {:name 'signed/map-sum-monotone-on :universes ['u]
   :type (function/forall
          [['A type-u] ['f function-type] ['g function-type]
           ['xs (list-of 'A)]
           ['dominated (all-at-most 'A 'f 'g 'xs)]]
          (sle (map-sum 'A 'f 'xs) (map-sum 'A 'g 'xs)))
   :value
   (function/lam
    [['A type-u] ['f function-type] ['g function-type]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam
          [['ys (list-of 'A)]]
          (function/forall
           [['dominated (all-at-most 'A 'f 'g 'ys)]]
           (sle (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys))))
         ;; nil : the empty sums are both zero
         (function/lam
          [['dominated (all-at-most 'A 'f 'g (nil-of 'A))]]
          (signed-at-most-reflexive signed-zero))
         ;; cons : split the conjunction and add the two comparisons
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (function/forall
                 [['dominated (all-at-most 'A 'f 'g 'tail)]]
                 (sle (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)))]
           ['dominated (all-at-most 'A 'f 'g (cons-of 'A 'head 'tail))]]
          (let [here (sle (app 'f 'head) (app 'g 'head))
                rest (all-at-most 'A 'f 'g 'tail)]
            (signed-add-monotone
             (app 'f 'head) (app 'g 'head)
             (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
             (prop-left here rest 'dominated)
             (app 'ih (prop-right here rest 'dominated)))))
         'xs))})

(def definition-specs [all-at-most-spec])
(def theorem-specs
  [all-at-most-empty-spec all-at-most-cons-spec all-at-most-combine-spec
   map-sum-monotone-on-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      sum/extend-environment
      (support/extend-with :signed-pointwise-order
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
