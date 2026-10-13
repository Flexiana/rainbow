(ns rainbow.math.finite.markov-hastings-diagonal
  "The canonical diagonal rejection placement, from a Boolean equality decider.

  The completed-Hastings-kernel theorems take the rejection placement as a
  PARAMETER with certificates, and the off-diagonal-zero corollary discharges
  the symmetry certificate -- but still asks the caller for a placement and for
  PROPOSITIONAL decidability of state equality.  That decidability is a
  Church-encoded disjunction, so it eliminates only into Prop: no placement
  FUNCTION can be built from it.  This module supplies the missing
  constructive half.

  Given a Boolean decider with soundness and completeness -- decide l r = true
  exactly when Eq l r -- the canonical placement puts the whole rejection mass
  on the diagonal:

      diagonal-placement decide mass x y = if (decide x y) then mass x else 0

  and three theorems make it plug directly into the existing corollaries: the
  placement is provably zero off the diagonal, carries exactly `mass x` on it,
  and the Boolean decider yields the PROPOSITIONAL decidability the symmetry
  corollary asks for.  The capstone then restates completed-kernel
  stationarity with the placement CONSTRUCTED rather than supplied: the caller
  provides the decider, its two laws, and the mass certificate for the
  diagonal function -- no separate placement, no symmetry certificate, no
  hand-written off-diagonal proof.

  For indexed state spaces this closes the practical gap entirely:
  nat/decide-equality with its existing true-sound and
  equality-implies-decide-equality-true theorems is precisely such a decider,
  and the test instantiates exactly that.

  Scope boundary, stated because the neighbouring cone is live: the exact
  ROW-TOTAL theorem -- that the diagonal placement's row over an enumeration
  sums to the single diagonal entry -- is NOT here.  It needs sum-over-
  enumeration machinery against finset no-duplicates evidence, which is the
  diagonal-spike route that was explored separately.  The mass certificate
  stays a hypothesis in the capstone for that reason.  Native and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-hastings-flow :as hastings]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- app [f & args] (apply function/app f args))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- state-equality [element left right]
  (function/equality data-u element left right))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- decider-type [element]
  (function/arrow element element bool))
(defn- mass-type [element] (function/arrow element nnrat))

(defn- sound-type
  "decide l r = true implies Eq l r."
  [element decide]
  (function/forall
   [['sound-left element] ['sound-right element]]
   (function/arrow (eq-bool (app decide 'sound-left 'sound-right) true-value)
                   (state-equality element 'sound-left 'sound-right))))

(defn- complete-type
  "Eq l r implies decide l r = true."
  [element decide]
  (function/forall
   [['complete-left element] ['complete-right element]]
   (function/arrow (state-equality element 'complete-left 'complete-right)
                   (eq-bool (app decide 'complete-left 'complete-right)
                            true-value))))

(defn- selected-nnrat [at-false at-true choice]
  (app (function/const* 'data/Bool.rec [type-level])
       (function/lam [['ignored bool]] nnrat)
       at-false at-true choice))

(def diagonal-placement-spec
  {:name 'mcmc/diagonal-placement :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]
     ['source 'S] ['destination 'S]]
    (selected-nnrat nnrat-zero (app 'mass 'source)
                    (app 'decide 'source 'destination)))})

(defn- placement [element decide mass]
  (app (function/const* 'mcmc/diagonal-placement [U]) element decide mass))

;; ---- pointwise laws ---------------------------------------------------------

(defn- bool-congruence
  "Eq nnrat (selected-nnrat zero m b) (selected-nnrat zero m b'), from Eq b b'."
  [mass-at left-bool right-bool proof]
  (app (function/const* 'equality/congruent-function [type-level type-level])
       bool nnrat
       (function/lam [['choice bool]] (selected-nnrat nnrat-zero mass-at 'choice))
       left-bool right-bool proof))

(defn- equivalent-from-equal
  "req value target, from Eq nnrat value target, by reverse substitution into
  reflexivity at target."
  [value target proof]
  (app (function/const* 'equality/reverse-substitution [type-level])
       nnrat value target proof
       (function/lam [['candidate nnrat]] (req 'candidate target))
       (app (function/const* 'nnrat/equivalent-reflexive []) target)))

(def diagonal-mass-spec
  "On the diagonal the placement is exactly the mass: completeness makes the
  decider answer true at (x, x), and one congruence collapses the selector."
  {:name 'mcmc/diagonal-placement-diagonal-mass :universes ['u]
   :type
   (function/forall
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]
     ['complete (complete-type 'S 'decide)]
     ['state 'S]]
    (req (app (placement 'S 'decide 'mass) 'state 'state)
         (app 'mass 'state)))
   :value
   (function/lam
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]
     ['complete (complete-type 'S 'decide)]
     ['state 'S]]
    (equivalent-from-equal
     (app (placement 'S 'decide 'mass) 'state 'state)
     (app 'mass 'state)
     (bool-congruence (app 'mass 'state)
                      (app 'decide 'state 'state) true-value
                      (app 'complete 'state 'state
                           (app (function/const* 'equality/reflexive [data-u])
                                'S 'state)))))})

(def off-diagonal-zero-mine-spec
  "Off the diagonal the placement is zero. The decider's verdict at (l, r) is
  case-split by Bool.rec at the motive `Eq (decide l r) b -> goal`, applied to
  reflexivity: the false case collapses the selector to zero by congruence,
  and the true case is refuted by soundness against the difference hypothesis."
  {:name 'mcmc/diagonal-placement-off-diagonal-zero :universes ['u]
   :type
   (function/forall
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]
     ['sound (sound-type 'S 'decide)]]
    (app (function/const* 'mcmc/nnrat-off-diagonal-zero [U])
         'S (placement 'S 'decide 'mass)))
   :value
   (function/lam
    [['S type-u] ['decide (decider-type 'S)] ['mass (mass-type 'S)]
     ['sound (sound-type 'S 'decide)]
     ['left 'S] ['right 'S]
     ['different (proposition/negation (state-equality 'S 'left 'right))]]
    (let [verdict (app 'decide 'left 'right)
          goal (req (app (placement 'S 'decide 'mass) 'left 'right)
                    nnrat-zero)]
      (app
       (app (function/const* 'data/Bool.rec [zero-level])
            (function/lam [['branch bool]]
                          (function/arrow (eq-bool verdict 'branch) goal))
            ;; false branch
            (function/lam [['is-false (eq-bool verdict false-value)]]
                          (equivalent-from-equal
                           (app (placement 'S 'decide 'mass) 'left 'right)
                           nnrat-zero
                           (bool-congruence (app 'mass 'left)
                                            verdict false-value 'is-false)))
            ;; true branch
            (function/lam [['is-true (eq-bool verdict true-value)]]
                          (app (function/const* 'proposition/explode [])
                               goal
                               (app 'different
                                    (app 'sound 'left 'right 'is-true))))
            verdict)
       (app (function/const* 'equality/reflexive [type-level]) bool verdict))))})

;; ---- the propositional bridge -----------------------------------------------

(def equality-decidable-of-boolean-spec
  "A sound and complete Boolean decider yields the PROPOSITIONAL decidability
  the symmetry corollary asks for: case on the verdict; true goes left by
  soundness, false goes right because completeness would force true."
  {:name 'mcmc/state-equality-decidable-of-boolean :universes ['u]
   :type
   (function/forall
    [['S type-u] ['decide (decider-type 'S)]
     ['sound (sound-type 'S 'decide)]
     ['complete (complete-type 'S 'decide)]
     ['left 'S] ['right 'S]]
    (proposition/disjunction
     (state-equality 'S 'left 'right)
     (proposition/negation (state-equality 'S 'left 'right))))
   :value
   (function/lam
    [['S type-u] ['decide (decider-type 'S)]
     ['sound (sound-type 'S 'decide)]
     ['complete (complete-type 'S 'decide)]
     ['left 'S] ['right 'S]]
    (let [same (state-equality 'S 'left 'right)
          different (proposition/negation same)
          verdict (app 'decide 'left 'right)
          goal (proposition/disjunction same different)]
      (app
       (app (function/const* 'data/Bool.rec [zero-level])
            (function/lam [['branch bool]]
                          (function/arrow (eq-bool verdict 'branch) goal))
            (function/lam
             [['is-false (eq-bool verdict false-value)]]
             (app (function/const* 'proposition/right-disjunct [])
                  same different
                  (function/lam
                   [['are-same same]]
                   (app (function/const* 'bool/false-not-true [])
                        (app (function/const* 'equality/transitive [type-level])
                             bool false-value verdict true-value
                             (app (function/const* 'equality/symmetric [type-level])
                                  bool verdict false-value 'is-false)
                             (app 'complete 'left 'right 'are-same))))))
            (function/lam
             [['is-true (eq-bool verdict true-value)]]
             (app (function/const* 'proposition/left-disjunct [])
                  same different
                  (app 'sound 'left 'right 'is-true)))
            verdict)
       (app (function/const* 'equality/reflexive [type-level]) bool verdict))))})

;; ---- the capstone -----------------------------------------------------------

(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- total-mass [element states weights]
  (app (function/const* 'probability/nnrat-total-mass [U]) element states weights))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- rejection-mass [element states target proposal source]
  (app (function/const* 'mcmc/nnrat-hastings-rejection-mass [U])
       element states target proposal source))
(defn- completed-kernel [element states target proposal the-placement]
  (app (function/const* 'mcmc/nnrat-hastings-completed-kernel [U])
       element states target proposal the-placement))
(defn- stationary [element states kernel target]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel target))

(def stationary-of-diagonal-placement-spec
  "Completed-kernel stationarity with the placement CONSTRUCTED. The caller
  supplies the decider with its two laws and the mass certificate for the
  DIAGONAL placement specifically; symmetry and off-diagonal-zero are
  discharged by the theorems above rather than asked for."
  {:name 'mcmc/nnrat-hastings-completed-kernel-stationary-of-diagonal-placement
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (mass-type 'S)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decide (decider-type 'S)]
     ['sound (sound-type 'S 'decide)]
     ['complete (complete-type 'S 'decide)]
     ['mass (mass-type 'S)]
     ['target-normalized (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['source 'S]]
       (req (total-mass 'S 'states
                        (app (placement 'S 'decide 'mass) 'source))
            (rejection-mass 'S 'states 'target 'proposal 'source)))]]
    (stationary 'S 'states
                (completed-kernel 'S 'states 'target 'proposal
                                  (placement 'S 'decide 'mass))
                'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (mass-type 'S)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decide (decider-type 'S)]
     ['sound (sound-type 'S 'decide)]
     ['complete (complete-type 'S 'decide)]
     ['mass (mass-type 'S)]
     ['target-normalized (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['source 'S]]
       (req (total-mass 'S 'states
                        (app (placement 'S 'decide 'mass) 'source))
            (rejection-mass 'S 'states 'target 'proposal 'source)))]]
    (app
     (function/const*
      'mcmc/nnrat-hastings-completed-kernel-stationary-of-off-diagonal-zero [U])
     'S 'states 'target 'proposal (placement 'S 'decide 'mass)
     (app (function/const* 'mcmc/state-equality-decidable-of-boolean [U])
          'S 'decide 'sound 'complete)
     (app (function/const* 'mcmc/diagonal-placement-off-diagonal-zero [U])
          'S 'decide 'mass 'sound)
     'target-normalized 'proposal-normalized
     'placement-has-rejection-mass))})

(def definition-specs [diagonal-placement-spec])
(def theorem-specs
  [diagonal-mass-spec
   off-diagonal-zero-mine-spec
   equality-decidable-of-boolean-spec
   stationary-of-diagonal-placement-spec])

(defn- require-alias [checked-environment alias]
  (when-not (environment/resolve-id checked-environment alias)
    (throw (ex-info "diagonal placement needs an alias the chain lacks"
                    {:missing alias}))))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-hastings-flow])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (let [extended checked-environment] (require-alias extended 'bool/false-not-true) (support/extend-with extended :finite-markov-hastings-diagonal (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.markov-hastings-diagonal))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
