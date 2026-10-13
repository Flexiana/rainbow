(ns rainbow.math.rational.nnrat.farkas-elim-affine-decidable
  "Brick 4b of the general LP strong-duality Fourier-Motzkin encoding
 : decidability of the one-variable
  affine-list elimination -- the Farkas-alternative half.

  Feasibility of the eliminated system (brick 4,
  nnrat_farkas_elim_affine_list.clj) is DECIDABLE: every affine row's
  coupling a*v + s <= b is a decidable nnrat comparison
  (nnrat/at-most-decidable), a finite conjunction of decidables is
  decidable, and the reduced condition is exactly that conjunction at
  max-lb. Transporting through the brick-4 solvable-iff equivalence yields
  decidable solvability. The negative branch is the infeasibility
  certificate -- the object that, in the objective-boundary system, becomes
  the dual once t exceeds the optimum. So this is the constructive
  Farkas alternative for affine-row systems, the certificate half of
  strong duality. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as affine-list]
            [rainbow.math.rational.nnrat.farkas-alternative :as alternative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
(def row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-row
  (function/app (function/const* 'data/List [type-level]) row))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- row-a [r] (first-of nnrat pair-nnrat r))
(defn- row-sb [r] (second-of nnrat pair-nnrat r))
(defn- row-s [r] (first-of nnrat nnrat (row-sb r)))
(defn- row-b [r] (second-of nnrat nnrat (row-sb r)))
(defn- coupling-at [r value]
  (at-most (add (multiply (row-a r) value) (row-s r)) (row-b r)))

(defn- rows-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows value))
(defn- reduced [lowers rows]
  (function/app (function/const* 'nnrat/farkas-elim-affine-list-reduced [])
                lowers rows))
(defn- solvable [lowers rows]
  (function/app (function/const* 'nnrat/farkas-elim-affine-list-solvable [])
                lowers rows))

(defn- negation [claim]
  (function/app (function/const* 'proposition/negation []) claim))
(defn- disjunction [left right]
  (function/app (function/const* 'proposition/disjunction []) left right))
(defn- decidable [claim] (disjunction claim (negation claim)))
(defn- conjunction [left right]
  (function/app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- left-disjunct [left right evidence]
  (function/app (function/const* 'proposition/left-disjunct [])
                left right evidence))
(defn- right-disjunct [left right evidence]
  (function/app (function/const* 'proposition/right-disjunct [])
                left right evidence))
(defn- use-disjunction [left right result evidence on-left on-right]
  (function/app (function/const* 'proposition/use-disjunction [])
                left right result evidence on-left on-right))
(defn- at-most-decidable [left right]
  (function/app (function/const* 'nnrat/at-most-decidable []) left right))
(defn- equivalence-forward [left right iff evidence]
  (function/app (function/const* 'proposition/equivalence-forward [])
                left right iff evidence))
(defn- equivalence-backward [left right iff evidence]
  (function/app (function/const* 'proposition/equivalence-backward [])
                left right iff evidence))

;; Decidability is closed under conjunction (the alternative module keeps
;; this local, so it is re-derived here).
(defn- conjunction-decision [left right left-decision right-decision]
  (let [both (conjunction left right)
        not-left (negation left)
        not-right (negation right)
        target (decidable both)]
    (use-disjunction
     left not-left target left-decision
     (function/lam
      [['left-proof left]]
      (use-disjunction
       right not-right target right-decision
       (function/lam
        [['right-proof right]]
        (left-disjunct both (negation both)
                       (conjoin left right 'left-proof 'right-proof)))
       (function/lam
        [['not-right-proof not-right]]
        (right-disjunct
         both (negation both)
         (function/lam
          [['both-proof both]]
          (function/app 'not-right-proof
                        (right-conjunct left right 'both-proof)))))))
     (function/lam
      [['not-left-proof not-left]]
      (right-disjunct
       both (negation both)
       (function/lam
        [['both-proof both]]
        (function/app 'not-left-proof
                      (left-conjunct left right 'both-proof))))))))

(defn- nil-row []
  (function/app (function/const* 'data/nil [type-level]) row))
(defn- cons-row [head tail]
  (function/app (function/const* 'data/cons [type-level]) row head tail))

(def rows-decidable-spec
  {:name 'nnrat/farkas-elim-affine-rows-decidable
   :universes []
   :type
   (function/forall
    [['rows list-row] ['value nnrat]]
    (decidable (rows-satisfied 'rows 'value)))
   :value
   (function/lam
    [['rows list-row] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level zero-level])
     row
     (function/lam [['rs list-row]] (decidable (rows-satisfied 'rs 'value)))
     ;; nil: rows-satisfied nil value reduces to truth, decided positively.
     (left-disjunct (rows-satisfied (nil-row) 'value)
                    (negation (rows-satisfied (nil-row) 'value))
                    (function/const* 'proposition/trivial []))
     (function/lam
      [['head row] ['tail list-row]
       ['ih (decidable (rows-satisfied 'tail 'value))]]
      (conjunction-decision
       (coupling-at 'head 'value)
       (rows-satisfied 'tail 'value)
       (at-most-decidable
        (add (multiply (row-a 'head) 'value) (row-s 'head))
        (row-b 'head))
       'ih))
     'rows))})

(def solvable-or-not-spec
  {:name 'nnrat/farkas-elim-affine-list-solvable-or-not
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['rows list-row]]
    (decidable (solvable 'lowers 'rows)))
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]]
    (let [red (reduced 'lowers 'rows)
          sol (solvable 'lowers 'rows)
          iff (function/app
               (function/const*
                'nnrat/farkas-elim-affine-list-solvable-iff [])
               'lowers 'rows)
          red-decision
          (function/app
           (function/const* 'nnrat/farkas-elim-affine-rows-decidable [])
           'rows (max-lb 'lowers))]
      (use-disjunction
       red (negation red) (decidable sol) red-decision
       (function/lam
        [['red-proof red]]
        (left-disjunct sol (negation sol)
                       (equivalence-forward red sol iff 'red-proof)))
       (function/lam
        [['not-red (negation red)]]
        (right-disjunct
         sol (negation sol)
         (function/lam
          [['sol-proof sol]]
          (function/app 'not-red
                        (equivalence-backward red sol iff 'sol-proof))))))))})

(def definition-specs [])
(def theorem-specs [rows-decidable-spec solvable-or-not-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      affine-list/extend-environment
      alternative/extend-environment
      (support/extend-with :nnrat-farkas-elim-affine-decidable
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
