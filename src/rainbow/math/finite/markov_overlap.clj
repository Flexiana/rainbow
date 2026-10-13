(ns rainbow.math.finite.markov-overlap
  "Shared-mass certificates for finite Dobrushin bounds.
  Equal input total mass gives normalized TV + common mass = input mass.
  For probability rows, a lower bound on common mass certifies an upper
  bound on the all-pairs coefficient, without rational subtraction."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-residual-coupling :as residual]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.rational.nnrat.map-sum-member :as member-sum]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat residual/nnrat)
(def one (c 'nnrat/one))
(def half (c 'nnrat/half))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- total [mass] (poly 'probability/nnrat-total-mass 'S 'states mass))
(defn- tv [a b] (poly 'markov/nnrat-normalized-total-variation 'S 'states a b))
(defn- l1 [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
(defn- common [a b]
  ;; a and b may already contain the outer row indices i and j.
  (total (f/lam [['overlap-state 'S]]
           (app 'minmax/min (f/app a 'overlap-state) (f/app b 'overlap-state)))))
(def equal-mass-binders
  (conj residual/base-binders ['same-total (eqv (total 'left) (total 'right))]))

(def normalized-tv-is-residual-total-spec
  (let [p (total (residual/residual-mapping :left)) q (total (residual/residual-mapping :right))
        lhs (tv 'left 'right) raw (mul half (add p q)) doubled (mul half (add p p))
        factored (mul (add half half) p) unit (mul one p)
        q-p (sym p q (poly 'markov/nnrat-residual-totals-equal 'S 'states 'left 'right 'same-total))
        halves-one (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) residual/nat
                     (app 'nat/multiply (app 'nnrat/numerator (add half half))
                          (app 'nnrat/denominator one)))]
    {:name 'markov/nnrat-normalized-tv-is-left-residual-total :universes ['u]
     :type (f/forall equal-mass-binders (eqv lhs p))
     :value
     (f/lam equal-mass-binders
       (trans lhs raw p
         (app 'nnrat/multiply-respects-equivalence half half (l1 'left 'right) (add p q)
              (refl half)
              (poly 'markov/nnrat-total-variation-is-residual-total-sum 'S 'states 'left 'right))
         (trans raw doubled p
           (app 'nnrat/multiply-respects-equivalence half half (add p q) (add p p)
                (refl half) (app 'nnrat/add-respects-equivalence p p q p (refl p) q-p))
           (trans doubled factored p (ring/equiv doubled factored)
             (trans factored unit p
               (app 'nnrat/multiply-respects-equivalence (add half half) one p p halves-one (refl p))
               (app 'nnrat/multiply-one-left p))))))}))

(def tv-plus-common-total-spec
  (let [p (total (residual/residual-mapping :left)) overlap (common 'left 'right)
        lhs (add (tv 'left 'right) overlap) middle (add p overlap)]
    {:name 'markov/nnrat-normalized-tv-plus-common-total :universes ['u]
     :type (f/forall equal-mass-binders (eqv lhs (total 'left)))
     :value
     (f/lam equal-mass-binders
       (trans lhs middle (total 'left)
         (app 'nnrat/add-respects-equivalence (tv 'left 'right) p overlap overlap
              (poly 'markov/nnrat-normalized-tv-is-left-residual-total
                    'S 'states 'left 'right 'same-total) (refl overlap))
         (poly 'markov/nnrat-left-residual-plus-common-total 'S 'states 'left 'right)))}))

(def normalized-tv-at-most-of-overlap-spec
  (let [overlap (common 'left 'right)
        bindings (into residual/base-binders
                       [['left-normalized (eqv (total 'left) one)]
                        ['right-normalized (eqv (total 'right) one)] ['rho nnrat]
                        ['overlap-budget (le one (add 'rho overlap))]])
        d (tv 'left 'right)
        same (trans (total 'left) one (total 'right) 'left-normalized
                    (sym (total 'right) one 'right-normalized))
        unit (trans (add d overlap) (total 'left) one
               (poly 'markov/nnrat-normalized-tv-plus-common-total
                     'S 'states 'left 'right same) 'left-normalized)]
    {:name 'markov/nnrat-normalized-tv-at-most-of-common-mass :universes ['u]
     :type (f/forall bindings (le d 'rho))
     :value (f/lam bindings
              (app 'nnrat/at-most-add-right-cancel d overlap 'rho
                (app 'nnrat/at-most-respects-equivalence
                  (add d overlap) one (add 'rho overlap) (add 'rho overlap)
                  unit (refl (add 'rho overlap)) 'overlap-budget)))}))

(defn- member [i]
  (poly 'list/membership 'S (poly 'finset-data/enumeration 'S 'states) i))
(def pair-binders [['i 'S] ['i-member (member 'i)] ['j 'S] ['j-member (member 'j)]])

(def common-total-at-least-listed-term-spec
  (let [a (f/app 'left 'target) b (f/app 'right 'target)
        minimum (app 'minmax/min a b)
        overlap (common 'left 'right)
        mapping (f/lam [['i 'S]] (app 'minmax/min (f/app 'left 'i) (f/app 'right 'i)))
        bindings (into residual/base-binders
                       [['target 'S] ['target-member (member 'target)] ['epsilon nnrat]
                        ['left-bound (le 'epsilon a)] ['right-bound (le 'epsilon b)]])]
    {:name 'markov/nnrat-common-total-at-least-listed-term :universes ['u]
     :type (f/forall bindings (le 'epsilon overlap))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-transitive 'epsilon minimum overlap
         (app 'minmax/at-most-min 'epsilon a b 'left-bound 'right-bound)
         (poly 'nnrat/map-sum-at-least-member 'S mapping
               (poly 'finset-data/enumeration 'S 'states) 'target 'target-member)))}))

(def coefficient-at-most-of-overlap-spec
  (let [row-i (f/app 'kernel 'i) row-j (f/app 'kernel 'j)
        bindings (into coefficient/base-binders
                       [['normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel)]
                        ['rho nnrat]
                        ['overlap-budget (f/forall pair-binders
                                           (le one (add 'rho (common row-i row-j))))]])
        rho (app 'signed/from-nnrat 'rho)]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-common-mass :universes ['u]
     :type (f/forall bindings
             (app 'signed/at-most (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel) rho))
     :value
     (f/lam bindings
       (poly 'markov/signed-kernel-dobrushin-coefficient-bounded 'S 'states 'kernel rho
         (app 'signed/from-nnrat-at-most (c 'nnrat/zero) 'rho (app 'nnrat/zero-at-most 'rho))
         (f/lam pair-binders
           (app 'signed/from-nnrat-at-most (tv row-i row-j) 'rho
             (poly 'markov/nnrat-normalized-tv-at-most-of-common-mass
                   'S 'states row-i row-j (f/app 'normalized 'i) (f/app 'normalized 'j) 'rho
                   (f/app 'overlap-budget 'i 'i-member 'j 'j-member))))))}))

(def coefficient-at-most-of-shared-column-spec
  (let [normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel)
        listed-row [['i 'S] ['i-member (member 'i)]]
        column-bound (f/forall listed-row (le 'epsilon (f/app 'kernel 'i 'target)))
        bindings (into coefficient/base-binders
                       [['normalized normalized] ['target 'S] ['target-member (member 'target)]
                        ['epsilon nnrat] ['rho nnrat] ['column-bound column-bound]
                        ['budget (le one (add 'rho 'epsilon))]])
        row-i (f/app 'kernel 'i) row-j (f/app 'kernel 'j)
        overlap (common row-i row-j)]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-shared-column :universes ['u]
     :type (f/forall bindings
             (app 'signed/at-most
                  (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
                  (app 'signed/from-nnrat 'rho)))
     :value
     (f/lam bindings
       (poly 'markov/signed-kernel-dobrushin-at-most-of-common-mass
         'S 'states 'kernel 'normalized 'rho
         (f/lam pair-binders
           (app 'nnrat/at-most-transitive one (add 'rho 'epsilon) (add 'rho overlap)
             'budget
             (app 'nnrat/add-monotone 'rho 'rho 'epsilon overlap
               (app 'nnrat/at-most-reflexive 'rho)
               (poly 'markov/nnrat-common-total-at-least-listed-term
                 'S 'states row-i row-j 'target 'target-member 'epsilon
                 (f/app 'column-bound 'i 'i-member)
                 (f/app 'column-bound 'j 'j-member)))))))}))

(def theorem-specs [normalized-tv-is-residual-total-spec tv-plus-common-total-spec
                    normalized-tv-at-most-of-overlap-spec common-total-at-least-listed-term-spec
                    coefficient-at-most-of-overlap-spec coefficient-at-most-of-shared-column-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-residual-coupling rainbow.math.finite.markov-dobrushin-kernel rainbow.math.rational.nnrat.map-sum-member])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-overlap theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-overlap))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
