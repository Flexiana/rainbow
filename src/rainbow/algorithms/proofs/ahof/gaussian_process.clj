(ns rainbow.algorithms.proofs.ahof.gaussian-process
  "AHoF O62 Gaussian Process (surrogate model / regression): the GP posterior mean at
  a query point is a kernel-weighted combination of the observed targets, the weights
  coming from the covariance between the query and the training points:

      posterior-mean w0 y0 w1 y1 = w0 * y0 + w1 * y1.

  Kernel weights 1/2, 1/2 on observations 1/2, 3/4 give the posterior mean 5/8; a query
  co-located with the first observation (weights 1, 0) returns it, 1/2. Values are
  proved by cross-product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gaussian-process`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def half (make-rational 1 1))
(def three-quarters (make-rational 3 3))
(def five-eighths (make-rational 5 7))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- posterior-mean [w0 y0 w1 y1]
  (function/app (function/const* 'gp/posterior-mean []) w0 y0 w1 y1))

(def posterior-mean-spec
  {:name 'gp/posterior-mean :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['y0 nnrat] ['w1 nnrat] ['y1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 'y0)
                                   (nnrat-multiply 'w1 'y1)))})

(def balanced-mean-spec
  {:name 'gp/balanced-mean :kind :definition :universes [] :type nnrat
   :value (posterior-mean half half half three-quarters)})
(def colocated-mean-spec
  {:name 'gp/colocated-mean :kind :definition :universes [] :type nnrat
   :value (posterior-mean nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [posterior-mean-spec balanced-mean-spec colocated-mean-spec])

(def posterior-mean-unfold-spec
  {:name 'gp/posterior-mean-unfold :universes []
   :type (function/forall [['w0 nnrat] ['y0 nnrat] ['w1 nnrat] ['y1 nnrat]]
                          (equality nnrat (posterior-mean 'w0 'y0 'w1 'y1)
                                    (nnrat-add (nnrat-multiply 'w0 'y0)
                                               (nnrat-multiply 'w1 'y1))))
   :value (function/lam [['w0 nnrat] ['y0 nnrat] ['w1 nnrat] ['y1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (posterior-mean 'w0 'y0 'w1 'y1)))})

(def balanced-is-five-eighths-spec
  {:name 'gp/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'gp/balanced-mean []) five-eighths)
   :value (equivalent-cross (function/const* 'gp/balanced-mean []) five-eighths)})

(def colocated-is-observation-spec
  {:name 'gp/colocated-is-observation :universes []
   :type (nnrat-equivalent (function/const* 'gp/colocated-mean []) half)
   :value (equivalent-cross (function/const* 'gp/colocated-mean []) half)})

(def gaussian-process-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type colocated-is-observation-spec)]
    {:name 'gp/gaussian-process :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'gp/balanced-is-five-eighths [])
                          (function/const* 'gp/colocated-is-observation []))}))

(def theorem-specs
  [posterior-mean-unfold-spec balanced-is-five-eighths-spec
   colocated-is-observation-spec gaussian-process-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-gaussian-process
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
