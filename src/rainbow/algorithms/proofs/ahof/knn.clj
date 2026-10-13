(ns rainbow.algorithms.proofs.ahof.knn
  "AHoF K-Nearest Neighbors (instance-based classification): classify a query
  point by a majority vote among its K nearest training examples -- a
  non-parametric method with no training phase (lazy learning). Given the per-class
  vote counts among the K neighbors, the predicted label is the class with the most
  votes:

      knn-predict votes = argmax_c votes(c)

  over exact-rational (integer) vote counts (returning the predicted class index),
  defined as the argmax-index fold over the class vote counts. Proved native and
  axiom-free, as worked instances: votes [2, 4, 1] predict class 1; and the worked
  certificates 2 <= 4 and 1 <= 4 (native nnrat/at-most). That the prediction is a
  plurality class for all vote vectors is not proved here; the distance
  computation and the K-nearest selection are executable.

  Requires argmax-index/argmax-index, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.knn`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- knn-predict [votes]
  (function/app (function/const* 'knn/predict []) votes))
(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; knn-predict votes = argmax_c votes(c)
(def predict-spec
  {:name 'knn/predict :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['votes list-nnrat]] (argmax-index-app 'votes))})

(def definition-specs [predict-spec])

;; Theorems -----------------------------------------------------------------

(def votes (nnrat-list (whole 2) (whole 4) (whole 1)))

;; Vote counts [2,4,1] among the K neighbors: class 1 has a plurality -> predict 1.
(def predicts-plurality-class-spec
  {:name 'knn/predicts-plurality-class :universes []
   :type (equality nat (knn-predict votes) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (knn-predict votes))})

;; Worked certificate: class 0's 2 votes are at most class 1's 4 (2 <= 4).
(def plurality-dominates-zero-spec
  {:name 'knn/plurality-dominates-zero :universes []
   :type (nnrat-at-most (whole 2) (whole 4))
   :value (at-most-proof (whole 2) (whole 4))})

;; ... and class 2 (1 <= 4).
(def plurality-dominates-two-spec
  {:name 'knn/plurality-dominates-two :universes []
   :type (nnrat-at-most (whole 1) (whole 4))
   :value (at-most-proof (whole 1) (whole 4))})

(def theorem-specs
  [predicts-plurality-class-spec plurality-dominates-zero-spec
   plurality-dominates-two-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      argmax-index/extend-environment
      (support/extend-with :ahof-knn
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
