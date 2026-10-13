(ns rainbow.math.rational.nnrat.distance-translation
  "Removing common nonnegative mass preserves exact rational distance.

  The proof uses the additive-radius characterization in both directions,
  additive monotonicity, and cancellation; no truncated subtraction is assumed."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]
            [rainbow.math.rational.nnrat.add-monotone :as monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as reassociation]
            [rainbow.math.rational.nnrat.metric-separation :as metric]))

(defn- c [name] (f/const* name []))
(defn- app [g & xs] (apply f/app g xs))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- add [a b] (app (c 'nnrat/add) a b))
(defn- dist [a b] (app (c 'nnrat/distance) a b))
(defn- le [a b] (app (c 'nnrat/at-most) a b))
(defn- eqv [a b] (app (c 'nnrat/equivalent) a b))
(defn- refl [a] (app (c 'nnrat/equivalent-reflexive) a))
(defn- sym [a b p] (app (c 'nnrat/equivalent-symmetric) a b p))
(defn- etrans [a b d p q] (app (c 'nnrat/equivalent-transitive) a b d p q))

(defn- swap-last [a b d]
  ;; (a+b)+d ~ (a+d)+b, transporting only rational equivalence.
  (etrans (add (add a b) d) (add a (add b d)) (add (add a d) b)
          (app (c 'nnrat/add-associative) a b d)
          (etrans (add a (add b d)) (add a (add d b)) (add (add a d) b)
                  (app (c 'nnrat/add-respects-equivalence)
                       a a (add b d) (add d b) (refl a)
                       (app (c 'nnrat/add-commutative) b d))
                  (sym (add (add a d) b) (add a (add d b))
                       (app (c 'nnrat/add-associative) a d b)))))

(defn- self-radius-bounds [a b]
  (let [radius (dist a b)
        left (le a (add b radius)) right (le b (add a radius))
        both (app (c 'nnrat/additive-closeness-of-distance-at-most)
                  a b radius (app (c 'nnrat/at-most-reflexive) radius))]
    [(app (c 'proposition/left) left right both)
     (app (c 'proposition/right) left right both)]))

(defn- shift-bound [a b common radius p]
  (app (c 'nnrat/at-most-respects-equivalence)
       (add a common) (add a common)
       (add (add b common) radius) (add (add b radius) common)
       (refl (add a common)) (swap-last b common radius)
       (app (c 'nnrat/add-right-monotone) common a (add b radius) p)))

(defn- cancel-bound [a b common radius p]
  (app (c 'nnrat/at-most-add-right-cancel) a common (add b radius)
       (app (c 'nnrat/at-most-respects-equivalence)
            (add a common) (add a common)
            (add (add b radius) common) (add (add b common) radius)
            (refl (add a common)) (swap-last b radius common) p)))

(def distance-add-right-spec
  {:name 'nnrat/distance-add-right :universes []
   :type (f/forall [['a nnrat] ['b nnrat] ['common nnrat]]
           (eqv (dist (add 'a 'common) (add 'b 'common)) (dist 'a 'b)))
   :value
   (f/lam [['a nnrat] ['b nnrat] ['common nnrat]]
     (let [shift-a (add 'a 'common) shift-b (add 'b 'common)
           radius (dist 'a 'b) shifted-radius (dist shift-a shift-b)
           [left right] (self-radius-bounds 'a 'b)
           [shift-left shift-right] (self-radius-bounds shift-a shift-b)]
       (app (c 'nnrat/at-most-antisymmetric) shifted-radius radius
            (app (c 'nnrat/distance-at-most-of-additive-closeness)
                 shift-a shift-b radius
                 (shift-bound 'a 'b 'common radius left)
                 (shift-bound 'b 'a 'common radius right))
            (app (c 'nnrat/distance-at-most-of-additive-closeness)
                 'a 'b shifted-radius
                 (cancel-bound 'a 'b 'common shifted-radius shift-left)
                 (cancel-bound 'b 'a 'common shifted-radius shift-right)))))})

(def definition-specs [])
(def theorem-specs [distance-add-right-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.metric-separation rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.additive-reassociation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-distance-translation theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.distance-translation))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
