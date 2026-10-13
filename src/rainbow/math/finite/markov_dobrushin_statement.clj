(ns rainbow.math.finite.markov-dobrushin-statement
  "Formal proposition for the finite Dobrushin contraction estimate.

  Registering this definition checks that the proposition is well formed.
  It does not inhabit that proposition or add a contraction axiom.
  The inhabitant is supplied separately by finite-markov-dobrushin-contraction."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (c 'nnrat/NonnegativeRational))
(def parameters (conj coefficient/base-binders ['rho nnrat]))
(defn- total [mass]
  (poly 'probability/nnrat-total-mass 'S 'states mass))
(defn- step [mass]
  (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
(defn- l1 [left right]
  (poly 'markov/nnrat-total-variation 'S 'states left right))

(def contraction-statement-spec
  {:name 'markov/nnrat-dobrushin-contraction-estimate
   :kind :definition :universes ['u]
   :type (f/forall parameters 'Prop)
   :value
   (f/lam parameters
     (f/forall
      [['normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel)]
       ['coefficient-bound
        (f/app (c 'signed/at-most)
               (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
               (f/app (c 'signed/from-nnrat) 'rho))]
       ['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]
       ['equal-total-mass (f/app (c 'nnrat/equivalent) (total 'left) (total 'right))]]
      (f/app (c 'nnrat/at-most)
             (l1 (step 'left) (step 'right))
             (f/app (c 'nnrat/multiply) 'rho (l1 'left 'right)))))})

(def definition-specs [contraction-statement-spec])
(def theorem-specs [])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-dobrushin-kernel])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-dobrushin-statement definition-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-dobrushin-statement))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
