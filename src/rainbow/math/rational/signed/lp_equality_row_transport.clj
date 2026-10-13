(ns rainbow.math.rational.signed.lp-equality-row-transport
  "Generic feasibility transport from an original equality to certified actual
  positive/negative row maps and RHS entries. All candidates, arbitrary finite
  index lists; no sign, distinctness or nonemptiness assumptions."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-equality-row :as row]
            [rainbow.math.rational.signed.multiply-ring :as multiply]))

(def U [:param 'u])
(def data-level [:succ U])
(def signed row/signed)
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- neg [v] (app 'signed/negate v))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- le [a b] (app 'signed/at-most a b))
(defn- both [P Q] (app 'proposition/conjunction P Q))
(defn- sym [a b proof] (app 'signed/equivalent-symmetric a b proof))
(defn- products [a] (f/lam [['i 'A]] (app 'signed/multiply (f/app a 'i) (f/app 'candidate 'i))))
(defn- objective [a] (poly 'signed/map-sum 'A (products a) 'indices))
(defn- objective-same [actual expected pointwise]
  (poly 'signed/map-sum-respects-equivalence 'A (products actual) (products expected)
        (f/lam [['i 'A]]
               (app 'signed/multiply-right-respects-equivalence
                    (f/app actual 'i) (f/app expected 'i) (f/app 'candidate 'i)
                    (f/app pointwise 'i))) 'indices))

(def actual-equality-row-equivalence-spec
  (let [maps (f/arrow 'A signed)
        negative-original (f/lam [['i 'A]] (neg (f/app 'original 'i)))
        bs [['A [:sort data-level]] ['original maps] ['positive maps] ['negative maps]
            ['indices (f/app (f/const* 'data/List [data-level]) 'A)]
            ['rhs signed] ['positive-rhs signed] ['negative-rhs signed]
            ['positive-same (f/forall [['i 'A]] (eqv (f/app 'positive 'i) (f/app 'original 'i)))]
            ['negative-same (f/forall [['i 'A]] (eqv (f/app 'negative 'i) (neg (f/app 'original 'i))))]
            ['positive-rhs-same (eqv 'positive-rhs 'rhs)]
            ['negative-rhs-same (eqv 'negative-rhs (neg 'rhs))]]
        cb [['candidate maps]]
        O (objective 'original) N (objective negative-original)
        P (objective 'positive) Q (objective 'negative)
        equality (eqv O 'rhs)
        upper (le O 'rhs) lower (le N (neg 'rhs))
        actual-upper (le P 'positive-rhs) actual-lower (le Q 'negative-rhs)
        actual (both actual-upper actual-lower)
        ps (objective-same 'positive 'original 'positive-same)
        ns (objective-same 'negative negative-original 'negative-same)
        forward
        (f/lam [['equal-row equality]]
               (let [ideal (poly 'signed/lp-equality-row-expand 'A 'original 'candidate 'indices 'rhs 'equal-row)]
                 (app 'proposition/conjoin actual-upper actual-lower
                      (app 'signed/at-most-respects-equivalence O P 'rhs 'positive-rhs
                           (sym P O ps) (sym 'positive-rhs 'rhs 'positive-rhs-same)
                           (app 'proposition/left upper lower ideal))
                      (app 'signed/at-most-respects-equivalence N Q (neg 'rhs) 'negative-rhs
                           (sym Q N ns) (sym 'negative-rhs (neg 'rhs) 'negative-rhs-same)
                           (app 'proposition/right upper lower ideal)))))
        backward
        (f/lam [['actual-rows actual]]
               (poly 'signed/lp-equality-row-contract 'A 'original 'candidate 'indices 'rhs
                     (app 'proposition/conjoin upper lower
                          (app 'signed/at-most-respects-equivalence P O 'positive-rhs 'rhs
                               ps 'positive-rhs-same (app 'proposition/left actual-upper actual-lower 'actual-rows))
                          (app 'signed/at-most-respects-equivalence Q N 'negative-rhs (neg 'rhs)
                               ns 'negative-rhs-same (app 'proposition/right actual-upper actual-lower 'actual-rows)))))]
    {:name 'signed/lp-actual-equality-row-equivalence :universes ['u]
     :type (f/forall (into bs cb) (app 'proposition/equivalence equality actual))
     :value (f/lam (into bs cb) (app 'proposition/equivalence-intro equality actual forward backward))}))

(def actual-inequality-row-equivalence-spec
  (let [maps (f/arrow 'A signed)
        bs [['A [:sort data-level]] ['original maps] ['actual maps]
            ['indices (f/app (f/const* 'data/List [data-level]) 'A)]
            ['rhs signed] ['actual-rhs signed]
            ['same (f/forall [['i 'A]] (eqv (f/app 'actual 'i) (f/app 'original 'i)))]
            ['rhs-same (eqv 'actual-rhs 'rhs)] ['candidate maps]]
        O (objective 'original) P (objective 'actual)
        original (le O 'rhs) actual (le P 'actual-rhs)
        summed (objective-same 'actual 'original 'same)]
    {:name 'signed/lp-actual-inequality-row-equivalence :universes ['u]
     :type (f/forall bs (app 'proposition/equivalence original actual))
     :value
     (f/lam bs
            (app 'proposition/equivalence-intro original actual
                 (f/lam [['holds original]]
                        (app 'signed/at-most-respects-equivalence O P 'rhs 'actual-rhs
                             (sym P O summed) (sym 'actual-rhs 'rhs 'rhs-same) 'holds))
                 (f/lam [['holds actual]]
                        (app 'signed/at-most-respects-equivalence P O 'actual-rhs 'rhs
                             summed 'rhs-same 'holds))))}))

(def theorem-specs [actual-equality-row-equivalence-spec actual-inequality-row-equivalence-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-equality-row rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-lp-equality-row-transport theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-equality-row-transport))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
