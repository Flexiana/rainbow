(ns rainbow.math.rational.nnrat.map-sum-zero
  "Every term of a vanishing finite nonnegative sum vanishes -- the sum-level form
  of nonnegativity-forces-zero, stated membership-free by positional split:

    nnrat/map-sum-zero-at-split :
      map-sum f (append ps (cons e qs)) ~ 0  ->  f e ~ 0

  i.e. if a sum over a list is ~ 0, the term at ANY position (identified by writing
  the list as ps ++ (e :: qs)) is ~ 0.  This is the sum-level complementary
  slackness fact: a zero gap = sum of nonnegative slack terms ~ 0 forces every
  individual slack to 0.

  Proof: map-sum-append rewrites the sum to (S ps) + ((f e) + (S qs)); two uses of
  add-zero-split (right then left) peel off (f e).  Polymorphic in the element
  type.  Native and axiom-free; chains nnrat-map-sum-append and
  nnrat-add-zero-split on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.map-sum-append :as ap]
            [rainbow.math.rational.nnrat.add-zero-split :as zs]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element] (function/app (function/const* 'data/List [data-level]) element))
(defn- appendl [A xs ys] (function/app (function/const* 'list/append [data-level]) A xs ys))
(defn- cons-of [element head tail]
  (function/app (function/const* 'data/cons [data-level]) element head tail))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-append [A f xs ys]
  (function/app (function/const* 'nnrat/map-sum-append [U]) A f xs ys))
(defn- split-left [a b h] (function/app (function/const* 'nnrat/add-zero-split-left []) a b h))
(defn- split-right [a b h] (function/app (function/const* 'nnrat/add-zero-split-right []) a b h))
(defn- app [f x] (function/app f x))

(def map-sum-zero-at-split-spec
  {:name 'nnrat/map-sum-zero-at-split :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)]
           ['ps (list-of 'A)] ['e 'A] ['qs (list-of 'A)]
           ['h (equiv (map-sum 'A 'f (appendl 'A 'ps (cons-of 'A 'e 'qs))) nnrat-zero)]]
          (equiv (app 'f 'e) nnrat-zero))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['ps (list-of 'A)] ['e 'A] ['qs (list-of 'A)]
     ['h (equiv (map-sum 'A 'f (appendl 'A 'ps (cons-of 'A 'e 'qs))) nnrat-zero)]]
    (let [sp (map-sum 'A 'f 'ps)
          tail-sum (map-sum 'A 'f (cons-of 'A 'e 'qs))   ; reduces to (f e) + S qs
          sq (map-sum 'A 'f 'qs)
          whole (map-sum 'A 'f (appendl 'A 'ps (cons-of 'A 'e 'qs)))
          ;; whole ~ sp + tail-sum
          app-eq (map-sum-append 'A 'f 'ps (cons-of 'A 'e 'qs))
          ;; (sp + tail-sum) ~ 0
          sum-zero (equiv-trans (radd sp tail-sum) whole nnrat-zero
                                (equiv-sym whole (radd sp tail-sum) app-eq)
                                'h)
          ;; tail-sum ~ 0  (= (f e) + sq ~ 0)
          tail-zero (split-right sp tail-sum sum-zero)]
      ;; f e ~ 0
      (split-left (app 'f 'e) sq tail-zero)))})

(def definition-specs [])
(def theorem-specs [map-sum-zero-at-split-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.map-sum-append rainbow.math.rational.nnrat.add-zero-split])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-map-sum-zero (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.map-sum-zero))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
