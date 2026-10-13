(ns rainbow.math.rational.signed.lp-free-price
  "Equality dual-price splitting over signed rationals.
  A certified p ~ pplus - pminus preserves every coefficient contribution.
  Component witnesses are nonnegative, but need not be the host max-based split
  for a noncanonical Grothendieck representative. No host execution claim."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.nnrat.farkas-elim-list :as zero-order]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.lp-objective-negate :as sense]))

(def signed (f/const* 'signed/SignedRational []))
(def zero (f/const* 'signed/zero []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- add [a b] (app 'signed/add a b))
(defn- mul [a b] (app 'signed/multiply a b))
(defn- neg [a] (app 'signed/negate a))
(defn- sub [a b] (app 'signed/subtract a b))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- trans [a b c ab bc] (app 'signed/equivalent-transitive a b c ab bc))
(defn- sym [a b ab] (app 'signed/equivalent-symmetric a b ab))
(defn- comm [a b] (app 'signed/multiply-commutative a b))
(defn- component [name p] (app 'signed/from-nnrat (app name p)))
(defn- plus [p] (component 'signed/positive p))
(defn- minus [p] (component 'signed/negative p))
(defn- expanded [v pp pm] (add (mul v pp) (mul (neg v) pm)))

(def free-price-split-contribution-spec
  (let [split (sub 'pp 'pm)
        bs [['v signed] ['p signed] ['pp signed] ['pm signed]
            ['same (eqv 'p split)]]]
    {:name 'signed/lp-free-price-split-contribution :universes []
     :type (f/forall bs (eqv (mul 'v 'p) (expanded 'v 'pp 'pm)))
     :value
     (f/lam
      bs
      (let [start (mul 'v 'p)
            flipped (mul 'p 'v)
            replaced (mul split 'v)
            distributed (add (mul 'pp 'v) (mul (neg 'pm) 'v))
            last-term (mul (neg 'v) 'pm)
            negative-product (neg (mul 'v 'pm))
            last-same
            (trans (mul (neg 'pm) 'v) (neg (mul 'pm 'v)) last-term
                   (app 'signed/multiply-negate-left 'pm 'v)
                   (trans (neg (mul 'pm 'v)) negative-product last-term
                          (app 'signed/negate-respects-equivalence
                               (mul 'pm 'v) (mul 'v 'pm) (comm 'pm 'v))
                          (sym last-term negative-product
                               (app 'signed/multiply-negate-left 'v 'pm))))]
        (trans start flipped (expanded 'v 'pp 'pm) (comm 'v 'p)
               (trans flipped replaced (expanded 'v 'pp 'pm)
                      (app 'signed/multiply-right-respects-equivalence 'p split 'v 'same)
                      (trans replaced distributed (expanded 'v 'pp 'pm)
                             (app 'signed/multiply-distributes-add-right 'pp (neg 'pm) 'v)
                             (app 'signed/add-respects-equivalence
                                  (mul 'pp 'v) (mul 'v 'pp)
                                  (mul (neg 'pm) 'v) last-term
                                  (comm 'pp 'v) last-same))))))}))

(def price-components-reconstruct-spec
  {:name 'signed/lp-price-components-reconstruct :universes []
   :type (f/forall [['p signed]] (eqv 'p (sub (plus 'p) (minus 'p))))
   :value
   (f/lam [['p signed]]
          (let [P (app 'signed/positive 'p) N (app 'signed/negative 'p)
                z (f/const* 'nnrat/zero [])]
            (ring/equiv (ring/radd P (ring/radd z N))
                        (ring/radd (ring/radd P z) N))))})

(def price-components-nonnegative-spec
  (let [pp (plus 'p) pm (minus 'p)
        P (app 'signed/at-most zero pp) Q (app 'signed/at-most zero pm)]
    {:name 'signed/lp-price-components-nonnegative :universes []
     :type (f/forall [['p signed]] (app 'proposition/conjunction P Q))
     :value
     (f/lam [['p signed]]
            (app 'proposition/conjoin P Q
                 (app 'signed/zero-at-most-of-nonnegative pp
                      (app 'nnrat/zero-at-most (app 'signed/positive 'p)))
                 (app 'signed/zero-at-most-of-nonnegative pm
                      (app 'nnrat/zero-at-most (app 'signed/negative 'p)))))}))

(def price-components-contribution-spec
  {:name 'signed/lp-price-components-contribution :universes []
   :type (f/forall [['v signed] ['p signed]]
                   (eqv (mul 'v 'p) (expanded 'v (plus 'p) (minus 'p))))
   :value
   (f/lam [['v signed] ['p signed]]
          (app 'signed/lp-free-price-split-contribution 'v 'p (plus 'p) (minus 'p)
               (app 'signed/lp-price-components-reconstruct 'p)))})

(def theorem-specs [free-price-split-contribution-spec price-components-reconstruct-spec
                    price-components-nonnegative-spec price-components-contribution-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-objective-negate rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/add-spec-shared :nnrat-farkas-elim-list zero-order/zero-at-most-spec) (support/extend-with :signed-lp-free-price theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-free-price))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
