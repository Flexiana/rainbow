(ns rainbow.math.rational.nnrat.farkas-eliminate-round
  "One full Fourier-Motzkin elimination round, composed
 : cross-product then reduction.

  Eliminating a variable v from a list of affine lower rows and a list of
  affine upper rows, brick 6's cross-product core
  (nnrat/farkas-cross-bilist-necessary) shows every pairwise cross condition
  holds, and the recursive reduction (nnrat/farkas-reduce-list-necessary)
  turns a both-sides cross-row list into a mixed affine-row system in one
  fewer variable. This composes them.

  The one seam between the two is STRUCTURAL, and this theorem makes it
  explicit rather than hiding it: the cross-product core emits cross
  conditions with OPAQUE survivor blocks, while the reduction consumes
  STRUCTURED both-sides rows A*v+P <= B*v+Q. Recognizing each cross
  condition's blocks as linear in the next variable is exactly the
  structured LP-system-as-data representation the n-variable capstone must
  supply. So the round takes that recognition as a hypothesis `link`
  (bilist cross conditions imply the both-sides row system holds); the
  capstone's representation discharges it. Given `link`,
  nnrat/farkas-eliminate-round proves the reduced affine system holds --
  the whole elimination round in one theorem. Native proof data,
  axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-cross-bilist :as bilist]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
;; lower/upper row: (a, (s, b)) / (a, (s, w))
(def affine-row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-affine
  (function/app (function/const* 'data/List [type-level]) affine-row))
;; both-sides row: (A, (B, (P, Q)))
(def bpq (function/app (function/const* 'data/Product [type-level type-level])
                       nnrat pair-nnrat))
(def bs-row (function/app (function/const* 'data/Product [type-level type-level])
                          nnrat bpq))
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))

(defn- lowers-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-lowers-satisfied []) rows value))
(defn- uppers-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows value))
(defn- bilist-conditions [lower-rows upper-rows]
  (function/app (function/const* 'nnrat/farkas-cross-bilist-conditions [])
                lower-rows upper-rows))
(defn- bilist-necessary [lower-rows upper-rows v lowers uppers]
  (function/app (function/const* 'nnrat/farkas-cross-bilist-necessary [])
                lower-rows upper-rows v lowers uppers))
(defn- both-sides-rows-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-both-sides-rows-satisfied [])
                rows value))
(defn- reduced-conditions [rows value]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows value))
(defn- reduce-list-necessary [rows value satisfied]
  (function/app (function/const* 'nnrat/farkas-reduce-list-necessary [])
                rows value satisfied))

(def eliminate-round-spec
  {:name 'nnrat/farkas-eliminate-round
   :universes []
   :type
   (function/forall
    [['lower-rows list-affine] ['upper-rows list-affine] ['v nnrat]
     ['bs-rows list-bs] ['w nnrat]
     ['link (function/arrow
             (bilist-conditions 'lower-rows 'upper-rows)
             (both-sides-rows-satisfied 'bs-rows 'w))]
     ['lowers (lowers-satisfied 'lower-rows 'v)]
     ['uppers (uppers-satisfied 'upper-rows 'v)]]
    (reduced-conditions 'bs-rows 'w))
   :value
   (function/lam
    [['lower-rows list-affine] ['upper-rows list-affine] ['v nnrat]
     ['bs-rows list-bs] ['w nnrat]
     ['link (function/arrow
             (bilist-conditions 'lower-rows 'upper-rows)
             (both-sides-rows-satisfied 'bs-rows 'w))]
     ['lowers (lowers-satisfied 'lower-rows 'v)]
     ['uppers (uppers-satisfied 'upper-rows 'v)]]
    ;; cross-product core -> bilist cross conditions
    (let [crosses (bilist-necessary 'lower-rows 'upper-rows 'v 'lowers 'uppers)
          ;; structural bridge -> both-sides row system holds
          both-sides (function/app 'link crosses)]
      ;; recursive reduction -> mixed affine-row system in one fewer variable
      (reduce-list-necessary 'bs-rows 'w both-sides)))})

(def definition-specs [])
(def theorem-specs [eliminate-round-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-cross-bilist rainbow.math.rational.nnrat.farkas-reduce-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-eliminate-round (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-eliminate-round))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
