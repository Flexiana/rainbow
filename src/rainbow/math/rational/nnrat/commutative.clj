(ns rainbow.math.rational.nnrat.commutative
  "Native commutativity of nonnegative-rational addition and multiplication, up
  to cross-multiplication equivalence. These make the exact-rational base a
  commutative structure and are the first general (non-worked-instance) rational
  algebra laws, assembled from the native nat commutativity lemmas. They let
  later signed and operations-research proofs reorder sums and products."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- predecessor [value]
  (function/app (function/const* 'nat/predecessor []) value))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- denominator-predecessor [value]
  (function/app (function/const* 'nnrat/denominator-predecessor []) value))

(defn- add-nat [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- eqn [left right]
  (function/equality type-level nat left right))

;; Equality plumbing over nat.
(defn- congr [mapping left right proof]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right proof))

(defn- transitive [left middle right p q]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right p q))

(defn- nat-add-commutative [left right]
  (function/app (function/const* 'nat/add-commutative []) left right))

(defn- nat-multiply-commutative [left right]
  (function/app (function/const* 'nat/multiply-commutative []) left right))

;; add-commutative -----------------------------------------------------------
;; equivalent (a+b) (b+a) unfolds to
;;   Eq nat (num(a+b) * denom(b+a)) (num(b+a) * denom(a+b))
;; where num(a+b) = (na*db) + (nb*da), denom(a+b) = succ(pred((succ dpa)*(succ dpb))).

(def add-commutative-spec
  {:name 'nnrat/add-commutative
   :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
                          (equivalent (nnrat-add 'a 'b) (nnrat-add 'b 'a)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [na (numerator 'a) da (denominator 'a)
          nb (numerator 'b) db (denominator 'b)
          dpa (denominator-predecessor 'a) dpb (denominator-predecessor 'b)
          term-a (multiply-nat na db)
          term-b (multiply-nat nb da)
          num-ab (add-nat term-a term-b)
          num-ba (add-nat term-b term-a)
          den-ab (denominator (nnrat-add 'a 'b))
          den-ba (denominator (nnrat-add 'b 'a))
          ;; numerator commutes: num-ab = num-ba
          num-comm (nat-add-commutative term-a term-b)
          ;; denominator: combine dpb dpa = pred((succ dpb)*(succ dpa)); commute.
          mul-comm (nat-multiply-commutative (succ dpb) (succ dpa))
          pred-comm (congr (function/lam [['m nat]] (predecessor 'm))
                           (multiply-nat (succ dpb) (succ dpa))
                           (multiply-nat (succ dpa) (succ dpb))
                           mul-comm)
          den-comm (congr (function/lam [['c nat]] (succ 'c))
                          (predecessor (multiply-nat (succ dpb) (succ dpa)))
                          (predecessor (multiply-nat (succ dpa) (succ dpb)))
                          pred-comm)
          ;; (num-ab * den-ba) = (num-ba * den-ba) via numerator commutativity
          left-step (congr (function/lam [['x nat]] (multiply-nat 'x den-ba))
                           num-ab num-ba num-comm)
          ;; (num-ba * den-ba) = (num-ba * den-ab) via denominator commutativity
          right-step (congr (function/lam [['d nat]] (multiply-nat num-ba 'd))
                            den-ba den-ab den-comm)]
      (transitive (multiply-nat num-ab den-ba)
                  (multiply-nat num-ba den-ba)
                  (multiply-nat num-ba den-ab)
                  left-step right-step)))})

;; multiply-commutative ------------------------------------------------------
;; equivalent (a*b) (b*a) unfolds to
;;   Eq nat (num(a*b) * denom(b*a)) (num(b*a) * denom(a*b))
;; where num(a*b) = na*nb, denom(a*b) = succ(pred((succ dpa)*(succ dpb))).

(def multiply-commutative-spec
  {:name 'nnrat/multiply-commutative
   :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
                          (equivalent (nnrat-multiply 'a 'b)
                                      (nnrat-multiply 'b 'a)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [na (numerator 'a) nb (numerator 'b)
          dpa (denominator-predecessor 'a) dpb (denominator-predecessor 'b)
          num-ab (multiply-nat na nb)
          num-ba (multiply-nat nb na)
          den-ab (denominator (nnrat-multiply 'a 'b))
          den-ba (denominator (nnrat-multiply 'b 'a))
          num-comm (nat-multiply-commutative na nb)
          mul-comm (nat-multiply-commutative (succ dpb) (succ dpa))
          pred-comm (congr (function/lam [['m nat]] (predecessor 'm))
                           (multiply-nat (succ dpb) (succ dpa))
                           (multiply-nat (succ dpa) (succ dpb))
                           mul-comm)
          den-comm (congr (function/lam [['c nat]] (succ 'c))
                          (predecessor (multiply-nat (succ dpb) (succ dpa)))
                          (predecessor (multiply-nat (succ dpa) (succ dpb)))
                          pred-comm)
          left-step (congr (function/lam [['x nat]] (multiply-nat 'x den-ba))
                           num-ab num-ba num-comm)
          right-step (congr (function/lam [['d nat]] (multiply-nat num-ba 'd))
                            den-ba den-ab den-comm)]
      (transitive (multiply-nat num-ab den-ba)
                  (multiply-nat num-ba den-ba)
                  (multiply-nat num-ba den-ab)
                  left-step right-step)))})

(def signed (function/const* 'signed/SignedRational []))

(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- add-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- nnrat-add-commutative [left right]
  (function/app (function/const* 'nnrat/add-commutative []) left right))

;; signed add-commutative: signed rationals form a commutative additive group up
;; to signed equivalence. The proof reuses nnrat add-commutativity componentwise
;; through nnrat/add-respects-equivalence.
(def signed-add-commutative-spec
  {:name 'signed/add-commutative
   :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (signed-equivalent (signed-add 'a 'b)
                                             (signed-add 'b 'a)))
   :value
   (function/lam
    [['a signed] ['b signed]]
    (let [pa (signed-positive 'a) pb (signed-positive 'b)
          na (signed-negative 'a) nb (signed-negative 'b)]
      (add-respects
       (nnrat-add pa pb) (nnrat-add pb pa)
       (nnrat-add nb na) (nnrat-add na nb)
       (nnrat-add-commutative pa pb)
       (nnrat-add-commutative nb na))))})

(def theorem-specs
  [add-commutative-spec multiply-commutative-spec signed-add-commutative-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "nnrat commutative expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :nnrat-commutative}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "nnrat commutative declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
