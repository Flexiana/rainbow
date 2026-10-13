(ns rainbow.math.rational.signed.gap-quality
  "Universal additive quality from a certified endpoint and reported gap.
  Arbitrary feasible sets/objectives; no optimizer existence or absolute-distance
  assertion. The conclusion includes feasibility of the submitted point."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-objective-negate :as foundations]
            [rainbow.math.rational.signed.additive-distance :as rearrange]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(def signed (f/const* 'signed/SignedRational []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- le [a b] (app 'signed/at-most a b))
(defn- add [a b] (app 'signed/add a b))
(defn- sub [a b] (app 'signed/subtract a b))
(defn- refl [a] (app 'signed/equivalent-reflexive a))
(defn- sym [a b h] (app 'signed/equivalent-symmetric a b h))
(defn- trans [a b c ab bc] (app 'signed/equivalent-transitive a b c ab bc))

(defn- quality-spec [minimum?]
  (let [fx (f/app 'objective 'x) fy (f/app 'objective 'y)
        candidate-bindings [['y 'A] ['member (f/app 'feasible 'y)]]
        bound (f/forall candidate-bindings (if minimum? (le 'endpoint fy) (le fy 'endpoint)))
        gap (if minimum? (eqv 'achieved (add 'endpoint 'gap)) (eqv 'endpoint (add 'achieved 'gap)))
        bindings [['A type-u] ['objective (f/arrow 'A signed)] ['feasible (f/arrow 'A 'Prop)]
                  ['x 'A] ['achieved signed] ['endpoint signed] ['gap signed] ['epsilon signed]
                  ['x-member (f/app 'feasible 'x)] ['achieved-same (eqv fx 'achieved)]
                  ['gap-same gap] ['bound bound] ['budget (le 'gap 'epsilon)]]
        difference (if minimum? (sub fx fy) (sub fy fx))
        all-quality (f/forall candidate-bindings (le difference 'epsilon))
        conclusion (app 'proposition/conjunction (f/app 'feasible 'x) all-quality)
        ;; First establish the correctly oriented additive inequality.
        additive
        (if minimum?
          (let [endpoint-plus-gap (add 'endpoint 'gap)
                endpoint-equality (trans fx 'achieved endpoint-plus-gap 'achieved-same 'gap-same)
                ordered (app 'signed/add-right-monotone 'endpoint fy 'gap (f/app 'bound 'y 'member))]
            (app 'signed/at-most-respects-equivalence endpoint-plus-gap fx (add fy 'gap) (add fy 'gap)
                 (sym fx endpoint-plus-gap endpoint-equality) (refl (add fy 'gap)) ordered))
          (let [transport (app 'signed/add-respects-equivalence 'achieved fx 'gap 'gap
                               (sym fx 'achieved 'achieved-same) (refl 'gap))
                endpoint-equality (trans 'endpoint (add 'achieved 'gap) (add fx 'gap) 'gap-same transport)]
            (app 'signed/at-most-respects-equivalence fy fy 'endpoint (add fx 'gap)
                 (refl fy) endpoint-equality (f/app 'bound 'y 'member))))
        raw-quality (app 'signed/subtract-at-most-of-additive-upper
                         (if minimum? fx fy) (if minimum? fy fx) 'gap additive)]
    {:name (if minimum? 'optimization/signed-lower-gap-epsilon-optimal
               'optimization/signed-upper-gap-epsilon-optimal)
     :universes ['u]
     :type (f/forall bindings conclusion)
     :value (f/lam bindings
                   (app 'proposition/conjoin (f/app 'feasible 'x) all-quality 'x-member
                        (f/lam candidate-bindings
                               (app 'signed/at-most-transitive difference 'gap 'epsilon raw-quality 'budget))))}))

(def upper-gap-epsilon-optimal-spec (quality-spec false))
(def lower-gap-epsilon-optimal-spec (quality-spec true))
(def theorem-specs [upper-gap-epsilon-optimal-spec lower-gap-epsilon-optimal-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-objective-negate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/add-spec-shared :signed-order-monotone monotone/add-right-monotone-spec) (support/add-spec-shared :signed-additive-distance rearrange/subtract-at-most-of-additive-upper-spec) (support/extend-with-shared :signed-gap-quality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.gap-quality))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
