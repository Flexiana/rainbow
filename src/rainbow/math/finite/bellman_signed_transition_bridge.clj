(ns rainbow.math.finite.bellman-signed-transition-bridge
  "Embed ordinary nonnegative transition kernels into signed Bellman proofs.

  The Grothendieck embedding preserves a finite map-sum, so an nnrat row whose
  total mass is one becomes a nonnegative normalized signed row.  The final
  theorem packages those bridge facts around the signed Bellman optimality
  contraction: callers may provide the natural nnrat transition kernel and its
  nnrat normalization proof, while rewards and value functions remain signed.

  This is the model-level refinement boundary needed by practical MDP data.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-optimal-contraction
             :as signed-contraction]
            [rainbow.math.finite.bellman-value-optimality :as nnrat-bellman]
            [rainbow.math.linear.matrix.affine-general-rate-certificate
             :as general-rate]
            [rainbow.math.linear.matrix.affine-strong-row-contraction
             :as strong-row]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas-list]
            [rainbow.math.rational.nnrat.list-sum :as nnrat-sum]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.geometric-bridge :as signed-bridge]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [level element]
  (app (function/const* 'data/List [level]) element))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- enumeration [level element source]
  (app (function/const* 'finset-data/enumeration [level]) element source))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- nnrat-map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- signed-map-sum [element mapping items]
  (app (function/const* 'signed/map-sum [U]) element mapping items))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- signed-total-mass [element source mass]
  (app (function/const* 'probability/signed-total-mass [U])
       element source mass))
(defn- nnrat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- nnrat-add [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- signed-equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- signed-equiv-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-add-respects [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime first second))

(def map-sum-from-nnrat-spec
  {:name 'signed/map-sum-from-nnrat
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['mapping (function/arrow 'A nnrat)]
     ['items (list-of data-u 'A)]]
    (signed-equivalent
     (signed-map-sum
      'A
      (function/lam [['item 'A]] (from-nnrat (app 'mapping 'item)))
      'items)
     (from-nnrat (nnrat-map-sum 'A 'mapping 'items))))
   :value
   (function/lam
    [['A type-u]
     ['mapping (function/arrow 'A nnrat)]
     ['items (list-of data-u 'A)]]
    (let [embedded
          (function/lam [['item 'A]] (from-nnrat (app 'mapping 'item)))]
      (app
       (function/const* 'data/List.rec [data-u zero-level])
       'A
       (function/lam
        [['remaining (list-of data-u 'A)]]
        (signed-equivalent
         (signed-map-sum 'A embedded 'remaining)
         (from-nnrat (nnrat-map-sum 'A 'mapping 'remaining))))
       (signed-equiv-reflexive signed-zero)
       (function/lam
        [['head 'A]
         ['tail (list-of data-u 'A)]
         ['induction
          (signed-equivalent
           (signed-map-sum 'A embedded 'tail)
           (from-nnrat (nnrat-map-sum 'A 'mapping 'tail)))]]
        (let [head-value (app 'mapping 'head)
              tail-sum (nnrat-map-sum 'A 'mapping 'tail)
              embedded-head (from-nnrat head-value)
              signed-tail (signed-map-sum 'A embedded 'tail)
              embedded-tail (from-nnrat tail-sum)
              middle (signed-add embedded-head embedded-tail)]
          (signed-equiv-transitive
           (signed-add embedded-head signed-tail)
           middle
           (from-nnrat (nnrat-add head-value tail-sum))
           (signed-add-respects
            embedded-head embedded-head signed-tail embedded-tail
            (signed-equiv-reflexive embedded-head) 'induction)
           (app (function/const* 'signed/from-nnrat-add [])
                head-value tail-sum))))
       'items)))} )

(def total-mass-from-nnrat-spec
  {:name 'probability/signed-total-mass-from-nnrat
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]]
    (signed-equivalent
     (signed-total-mass
      'A 'source
      (function/lam [['item 'A]] (from-nnrat (app 'mass 'item))))
     (from-nnrat (nnrat-total-mass 'A 'source 'mass))))
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]]
    (app (function/const* 'signed/map-sum-from-nnrat [U])
         'A 'mass (enumeration U 'A 'source)))})

(def embedded-mass-nonnegative-spec
  {:name 'probability/signed-embedded-mass-nonnegative
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mass (function/arrow 'A nnrat)]]
    (function/forall
     [['item 'A]]
     (signed-at-most signed-zero (from-nnrat (app 'mass 'item)))))
   :value
   (function/lam
    [['A type-u] ['mass (function/arrow 'A nnrat)] ['item 'A]]
    (app (function/const* 'signed/zero-at-most-from-nnrat [])
         (app 'mass 'item)))})

(def normalized-total-mass-from-nnrat-spec
  {:name 'probability/signed-total-mass-normalized-from-nnrat
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['normalized
      (nnrat-equivalent (nnrat-total-mass 'A 'source 'mass) nnrat-one)]]
    (signed-equivalent
     (signed-total-mass
      'A 'source
      (function/lam [['item 'A]] (from-nnrat (app 'mass 'item))))
     signed-one))
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['normalized
      (nnrat-equivalent (nnrat-total-mass 'A 'source 'mass) nnrat-one)]]
    (let [total (nnrat-total-mass 'A 'source 'mass)
          embedded-total (from-nnrat total)]
      (signed-equiv-transitive
       (signed-total-mass
        'A 'source
        (function/lam [['item 'A]] (from-nnrat (app 'mass 'item))))
       embedded-total signed-one
       (app (function/const* 'probability/signed-total-mass-from-nnrat [U])
            'A 'source 'mass)
       (app (function/const* 'signed/from-nnrat-respects-equivalence [])
            total nnrat-one 'normalized))))})

(def embedded-optimality-step-additively-contractive-spec
  (let [embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat 'discount)
        backup
        (function/lam
         [['value (function/arrow 'S signed)]
          ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward embedded-discount
              'value 'state 'action))
        optimality-step
        (fn [value state]
          (app (function/const* 'value/signed-optimality-step [U V])
               'S 'A 'actions 'fallback backup value state))
        contracted-epsilon (signed-multiply embedded-discount 'epsilon)]
    {:name 'value/nnrat-transition-signed-optimality-step-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (signed-at-most
          (app 'left-value 'state)
          (signed-add (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (signed-at-most
          (app 'right-value 'state)
          (signed-add (app 'left-value 'state) 'epsilon)))]]
      (function/forall
       [['state 'S]]
       (proposition/conjunction
        (signed-at-most
         (optimality-step 'left-value 'state)
         (signed-add
          (optimality-step 'right-value 'state) contracted-epsilon))
        (signed-at-most
         (optimality-step 'right-value 'state)
         (signed-add
          (optimality-step 'left-value 'state) contracted-epsilon)))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (signed-at-most
          (app 'left-value 'state)
          (signed-add (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (signed-at-most
          (app 'right-value 'state)
          (signed-add (app 'left-value 'state) 'epsilon)))]]
      (app
       (function/const*
        'value/signed-optimality-step-additively-contractive [U V])
       'S 'A 'states 'actions embedded-transition 'reward embedded-discount
       (app (function/const* 'signed/zero-at-most-from-nnrat []) 'discount)
       'fallback 'fallback-admissible
       (function/lam
        [['state 'S] ['action 'A] ['next-state 'S]]
        (app (function/const* 'signed/zero-at-most-from-nnrat [])
             (app 'transition 'state 'action 'next-state)))
       (function/lam
        [['state 'S] ['action 'A]]
        (app
         (function/const*
          'probability/signed-total-mass-normalized-from-nnrat [U])
         'S 'states (app 'transition 'state 'action)
         (app 'normalized 'state 'action)))
       'left-value 'right-value 'epsilon
       'left-pointwise 'right-pointwise))}))

(def definition-specs [])
(def theorem-specs
  [map-sum-from-nnrat-spec
   total-mass-from-nnrat-spec
   embedded-mass-nonnegative-spec
   normalized-total-mass-from-nnrat-spec
   embedded-optimality-step-additively-contractive-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-optimal-contraction])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :nnrat-list-sum (concat nnrat-sum/definition-specs nnrat-sum/theorem-specs)) (extend-specs-if-missing :finite-bellman-value-optimality [nnrat-bellman/total-mass-spec]) (extend-specs-if-missing :signed-geometric-bridge [signed-bridge/from-nnrat-respects-equivalence-spec signed-bridge/from-nnrat-at-most-spec]) (extend-specs-if-missing :nnrat-farkas-elim-list [farkas-list/zero-at-most-spec]) (extend-specs-if-missing :finite-matrix-affine-strong-row-contraction [strong-row/zero-at-most-from-nnrat-spec]) (extend-specs-if-missing :finite-matrix-affine-general-rate-certificate [general-rate/from-nnrat-add-spec]) (support/extend-with :finite-bellman-signed-transition-bridge theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-transition-bridge))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
