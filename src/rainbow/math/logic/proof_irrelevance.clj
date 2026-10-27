(ns rainbow.math.logic.proof-irrelevance
  "Proof irrelevance from propositional extensionality.

  `logic/proof-irrelevance-from-proposition-extensionality` has exactly the
  statement of the axiom `logic/proof-irrelevance` (rainbow.math.profile):

      forall {claim : Prop} (left right : claim), Eq.{0} claim left right

  and its kernel axiom closure is exactly #{logic/proposition-extensionality}.
  This is the CIC result that propositional extensionality implies proof
  irrelevance (Coq: Coq.Logic.ClassicalFacts, ext_prop_dep_proof_irrel_cic).
  It uses neither excluded middle, nor choice, nor proof irrelevance itself.

  Route:
  1. `logic/PropUnit : Prop`, an inductive proposition with one constructor
     `logic/prop-unit` and no fields. Its generated recursor
     `logic/PropUnit.rec` takes a dependent motive `PropUnit -> Sort m`; every
     motive below is into Prop, so no large elimination is involved (and the
     kernel's large-elimination rule only restricts blocks with two or more
     constructors anyway).
  2. `logic/prop-unit-eq-point`: every x : PropUnit equals prop-unit (recursor
     with motive fun z => Eq PropUnit z prop-unit, case reflexivity).
  3. `logic/prop-unit-proofs-equal`: any two x y : PropUnit are equal
     (recursor on x, then on y; the last case is reflexivity). Axiom-free.
  4. `logic/prop-unit-equals-inhabited`: an inhabited claim (p : claim) is
     equivalent to PropUnit (fun _ => p and fun _ => prop-unit), so by
     `logic/proposition-extensionality` Eq.{1} Prop PropUnit claim.
  5. `logic/prop-unit-transport-proofs-equal`: Leibniz transport along
     Eq Prop PropUnit claim with motive fun Q => forall x y : Q, Eq Q x y turns
     step 3 into proof irrelevance for claim. Axiom-free.
  6. The theorem: steps 4 and 5 at claim, using `left` itself as the
     inhabitant p.

  How the proofs were found (rainbow.core/prove and search/prove with a
  reuse/build-index index and the proving loop's candidate options): the
  search found steps 4 and 5 unaided once the earlier lemmas were indexed, and
  closed the reflexivity cases of steps 2 and 3 after an AI-proposed
  `intro`/`induction` decomposition (the search's native inductive cases cover
  only a fixed list of data types, so it never inducts on PropUnit itself).
  `logic/prop-unit-holds` and the final assembly (step 6) were hand-written:
  the search returned them as blockers, the first because no constructor of a
  new block is offered as an exact candidate, the second because applying a
  lemma with dependent binders fails with :tactic/dependent-apply-unsupported.
  Each value below is the kernel term the loop returned, written in surface
  syntax; the test checks the statement and the axiom closures."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as p]
            [rainbow.module :as module]))

(def prop-unit-block
  {:block/schema-version 1
   :block/alias 'logic/PropUnit
   :block/universes []
   :block/parameters []
   :block/sort-level [:zero]
   :block/constructors [{:constructor/alias 'logic/prop-unit :constructor/fields []}]})

(def ^:private PU (p/const* 'logic/PropUnit []))
(def ^:private point (p/const* 'logic/prop-unit []))
(defn- rec [motive case target]
  (p/app (p/const* 'logic/PropUnit.rec [[:zero]]) motive case target))
(defn- eq0 [carrier left right] (p/equality [:zero] carrier left right))
(defn- eq-prop [left right] (p/equality [:succ [:zero]] 'Prop left right))
(def ^:private reflexive-point
  (p/app (p/const* 'equality/reflexive [[:zero]]) PU point))
(def ^:private proofs-equal-motive
  (p/lam [['Q 'Prop]] (p/forall [['x 'Q] ['y 'Q]] (eq0 'Q 'x 'y))))

(def theorem-specs
  [{:name 'logic/prop-unit-holds
    :universes []
    :type PU
    :value point}

   {:name 'logic/prop-unit-eq-point
    :universes []
    :type (p/forall [['x PU]] (eq0 PU 'x point))
    :value (p/lam [['x PU]]
                  (rec (p/lam [['z PU]] (eq0 PU 'z point)) reflexive-point 'x))}

   {:name 'logic/prop-unit-proofs-equal
    :universes []
    :type (p/forall [['x PU] ['y PU]] (eq0 PU 'x 'y))
    :value (p/lam [['x PU] ['y PU]]
                  (rec (p/lam [['z PU]] (eq0 PU 'z 'y))
                       (rec (p/lam [['w PU]]
                                   (p/app (p/lam [['z PU]] (eq0 PU 'z 'w)) point))
                            reflexive-point 'y)
                       'x))}

   {:name 'logic/prop-unit-equals-inhabited
    :universes []
    :type (p/forall [['claim 'Prop] ['evidence 'claim]] (eq-prop PU 'claim))
    :value (p/lam [['claim 'Prop] ['evidence 'claim]]
                  (p/app (p/const* 'logic/proposition-extensionality []) PU 'claim
                         (p/introduce-equivalence
                          PU 'claim
                          (p/lam [['_unit PU]] 'evidence)
                          (p/lam [['_claim 'claim]]
                                 (p/const* 'logic/prop-unit-holds [])))))}

   {:name 'logic/prop-unit-transport-proofs-equal
    :universes []
    :type (p/forall [['claim 'Prop] ['same (eq-prop PU 'claim)]
                     ['x 'claim] ['y 'claim]]
                    (eq0 'claim 'x 'y))
    :value (p/lam [['claim 'Prop] ['same (eq-prop PU 'claim)]]
                  (p/app 'same proofs-equal-motive
                         (p/const* 'logic/prop-unit-proofs-equal [])))}

   {:name 'logic/proof-irrelevance-from-proposition-extensionality
    :universes []
    :type (p/forall [['claim 'Prop :implicit] ['left 'claim] ['right 'claim]]
                    (eq0 'claim 'left 'right))
    :value (p/lam [['claim 'Prop :implicit] ['left 'claim] ['right 'claim]]
                  (p/app (p/const* 'logic/prop-unit-transport-proofs-equal [])
                         'claim
                         (p/app (p/const* 'logic/prop-unit-equals-inhabited [])
                                'claim 'left)
                         'left 'right))}])

(def deps
  "Modules this one installs on top of (see rainbow.module). It needs only
  Leibniz equality, the propositional connectives and the declared axiom
  logic/proposition-extensionality, which the default checkpoint has and
  `rainbow.math.profile/activate` adds."
  '[])

(defn install
  "Adds PropUnit and this module's theorems. Refuses an environment without
  logic/proposition-extensionality rather than adding the axiom silently."
  [env]
  (when-not (environment/resolve-id env 'logic/proposition-extensionality)
    (throw (ex-info "logic/proposition-extensionality is not declared; activate the :propositional-extensional profile first"
                    {:error/category :module/missing-axiom})))
  (let [block-id (environment/resolve-id env 'logic/PropUnit)
        installed? (every? #(environment/resolve-id env (:name %)) theorem-specs)]
    (cond
      (and block-id installed?) env
      (or block-id installed?)
      (throw (ex-info "PropUnit package is partially installed"
                      {:block-installed? (boolean block-id) :theorems-installed? installed?}))
      :else
      (let [added (kernel/add-inductive-block env prop-unit-block)]
        (when-not (= :accepted (:status added))
          (throw (ex-info "PropUnit inductive block rejected" {:result added})))
        (support/extend-with (:environment added)
                             :proof-irrelevance-from-proposition-extensionality
                             theorem-specs)))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.logic.proof-irrelevance))

(defn theorem-ids [env] (support/spec-ids env theorem-specs))
