(ns rainbow.math.rational.nnrat.shared-residual-mass
  "Canonical common/residual decomposition, computed without choice.

  c=min(a,b), p=distance(c,a), q=distance(c,b). Then c+p~a,
  c+q~b, at least one residual is zero, and distance(a,b)~p+q."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distance-translation :as translation]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.nnrat.ordered-distance :as ordered]))

(defn- c [name] (f/const* name []))
(defn- app [g & xs] (apply f/app g xs))
(def nnrat (c 'nnrat/NonnegativeRational))
(def rzero (c 'nnrat/zero))
(def bindings [['a nnrat] ['b nnrat]])
(defn- add [a b] (app (c 'nnrat/add) a b))
(defn- dist [a b] (app (c 'nnrat/distance) a b))
(defn- eqv [a b] (app (c 'nnrat/equivalent) a b))
(defn- common [a b] (app (c 'minmax/min) a b))
(defn- left [a b] (app (c 'nnrat/left-residual-mass) a b))
(defn- right [a b] (app (c 'nnrat/right-residual-mass) a b))
(defn- refl [a] (app (c 'nnrat/equivalent-reflexive) a))
(defn- sym [a b p] (app (c 'nnrat/equivalent-symmetric) a b p))
(defn- trans [a b d p q] (app (c 'nnrat/equivalent-transitive) a b d p q))
(defn- self-zero [a]
  (app (c 'nnrat/distance-zero-of-equivalent) a a (refl a)))
(defn- zero-left [a]
  (trans (add rzero a) (add a rzero) a
         (app (c 'nnrat/add-commutative) rzero a)
         (app (c 'nnrat/add-zero-right) a)))

(def left-residual-mass-spec
  {:name 'nnrat/left-residual-mass :kind :definition :universes []
   :type (f/forall bindings nnrat)
   :value (f/lam bindings (dist (common 'a 'b) 'a))})
(def right-residual-mass-spec
  {:name 'nnrat/right-residual-mass :kind :definition :universes []
   :type (f/forall bindings nnrat)
   :value (f/lam bindings (dist (common 'a 'b) 'b))})

(def shared-plus-left-residual-spec
  {:name 'nnrat/shared-plus-left-residual :universes []
   :type (f/forall bindings (eqv (add (common 'a 'b) (left 'a 'b)) 'a))
   :value (f/lam bindings
            (app (c 'nnrat/add-distance-of-at-most) (common 'a 'b) 'a
                 (app (c 'minmax/min-lower-left) 'a 'b)))})
(def shared-plus-right-residual-spec
  {:name 'nnrat/shared-plus-right-residual :universes []
   :type (f/forall bindings (eqv (add (common 'a 'b) (right 'a 'b)) 'b))
   :value (f/lam bindings
            (app (c 'nnrat/add-distance-of-at-most) (common 'a 'b) 'b
                 (app (c 'minmax/min-lower-right) 'a 'b)))})

(defn- split-min [goal false-proof true-proof]
  (let [bool (c 'data/Bool)
        selected (fn [choice]
                   (app (f/const* 'data/Bool.rec [[:succ [:zero]]])
                        (f/lam [['ignored bool]] nnrat) 'b 'a choice))]
    (app (f/const* 'data/Bool.rec [[:zero]])
         (f/lam [['choice bool]] (goal (selected 'choice)))
         false-proof true-proof (app (c 'audit/decide-nnrat-at-most) 'a 'b))))

(def residuals-disjoint-spec
  (let [goal (fn [shared]
               (app (c 'proposition/disjunction)
                    (eqv (dist shared 'a) rzero) (eqv (dist shared 'b) rzero)))]
    {:name 'nnrat/residual-masses-disjoint :universes []
     :type (f/forall bindings (goal (common 'a 'b)))
     :value
     (f/lam bindings
       (split-min goal
                  (app (c 'proposition/right-disjunct)
                       (eqv (dist 'b 'a) rzero) (eqv (dist 'b 'b) rzero)
                       (self-zero 'b))
                  (app (c 'proposition/left-disjunct)
                       (eqv (dist 'a 'a) rzero) (eqv (dist 'a 'b) rzero)
                       (self-zero 'a))))}))

(def residual-distance-spec
  (let [shared (common 'a 'b) p (left 'a 'b) q (right 'a 'b)
        ps (add p shared) qs (add q shared)]
    {:name 'nnrat/residual-masses-preserve-distance :universes []
     :type (f/forall bindings (eqv (dist p q) (dist 'a 'b)))
     :value
     (f/lam bindings
       (trans (dist p q) (dist ps qs) (dist 'a 'b)
              (sym (dist ps qs) (dist p q)
                   (app (c 'nnrat/distance-add-right) p q shared))
              (app (c 'nnrat/distance-respects-equivalence) ps 'a qs 'b
                   (trans ps (add shared p) 'a
                          (app (c 'nnrat/add-commutative) p shared)
                          (app (c 'nnrat/shared-plus-left-residual) 'a 'b))
                   (trans qs (add shared q) 'b
                          (app (c 'nnrat/add-commutative) q shared)
                          (app (c 'nnrat/shared-plus-right-residual) 'a 'b)))))}))

(def distance-is-residual-sum-spec
  (let [goal (fn [shared]
               (eqv (dist 'a 'b) (add (dist shared 'a) (dist shared 'b))))
        ab (dist 'a 'b) ba (dist 'b 'a)
        bb (dist 'b 'b) aa (dist 'a 'a)]
    {:name 'nnrat/distance-is-residual-mass-sum :universes []
     :type (f/forall bindings (goal (common 'a 'b)))
     :value
     (f/lam bindings
       (split-min
        goal
        (trans ab ba (add ba bb)
               (app (c 'nnrat/distance-symmetric) 'a 'b)
               (sym (add ba bb) ba
                    (trans (add ba bb) (add ba rzero) ba
                           (app (c 'nnrat/add-respects-equivalence)
                                ba ba bb rzero (refl ba) (self-zero 'b))
                           (app (c 'nnrat/add-zero-right) ba))))
        (sym (add aa ab) ab
             (trans (add aa ab) (add rzero ab) ab
                    (app (c 'nnrat/add-respects-equivalence)
                         aa rzero ab ab (self-zero 'a) (refl ab))
                    (zero-left ab)))))}))

(def definition-specs [left-residual-mass-spec right-residual-mass-spec])
(def theorem-specs [shared-plus-left-residual-spec shared-plus-right-residual-spec
                    residuals-disjoint-spec residual-distance-spec
                    distance-is-residual-sum-spec])
(defn extend-environment [env]
  (-> env translation/extend-environment ordered/extend-environment
      minmax/extend-environment
      (support/extend-with :nnrat-shared-residual-mass
                           (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
