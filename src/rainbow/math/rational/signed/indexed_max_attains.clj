(ns rainbow.math.rational.signed.indexed-max-attains
  "Attainment for the index-aware max -- the other half of argmax correctness (with dominance).
     signed/max-is-left-or-right : forall a b, (max a b = a) or (max a b = b)   (Bool.rec on the decision)
     signed/indexed-max-from-attains :
       forall env init n, (indexed-max-from env init n = init)
                          or (exists i, strict-below i n AND indexed-max-from env init n = env i).
  The aggregate is either the fallback init or an actual input at some index below n. By induction on
  n via max-is-left-or-right, the IH, and the nat weakening/self lemmas. Off the trusted base."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.indexed-max :as imaxmod]
            [rainbow.math.nat.strict-below-more :as more]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private prop-level [:zero])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private environment-type (function/arrow nat signed))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- decide-at-most [a b] (app (function/const* 'signed/decide-at-most []) a b))
(defn- selected-at [af at choice]
  (app (function/const* 'data/Bool.rec [ulvl]) (function/lam [['ignored bool]] signed) af at choice))
(defn- eqs [x y] (app (function/const* 'equality/Eq [ulvl]) signed x y))
(defn- refls [x] (app (function/const* 'equality/reflexive [ulvl]) signed x))
(defn- syms [a b h] (app (function/const* 'equality/symmetric [ulvl]) signed a b h))
(defn- trs [a b c h1 h2] (app (function/const* 'equality/transitive [ulvl]) signed a b c h1 h2))
(defn- imax-from [env init n] (app (function/const* 'signed/indexed-max-from []) env init n))
(defn- strict-below [v u] (app (function/const* 'nat/strict-below []) v u))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- conj-t [l r] (app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r hl hr] (app (function/const* 'proposition/conjoin []) l r hl hr))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- existence [pred] (app (function/const* 'proposition/existence [ulvl]) nat pred))
(defn- witness [pred value evidence]
  (app (function/const* 'proposition/witness [ulvl]) nat pred value evidence))

(def max-is-left-or-right-spec
  {:name 'signed/max-is-left-or-right
   :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (disjt (eqs (smax 'a 'b) 'a) (eqs (smax 'a 'b) 'b)))
   :value (function/lam
           [['a signed] ['b signed]]
           (app (function/const* 'data/Bool.rec [prop-level])
                (function/lam [['bv bool]]
                              (disjt (eqs (selected-at 'a 'b 'bv) 'a) (eqs (selected-at 'a 'b 'bv) 'b)))
                (left-disj (eqs 'a 'a) (eqs 'a 'b) (refls 'a))     ; decision false -> selected = a
                (right-disj (eqs 'b 'a) (eqs 'b 'b) (refls 'b))    ; decision true  -> selected = b
                (decide-at-most 'a 'b)))})

(defn- max-lr [a b] (app (function/const* 'signed/max-is-left-or-right []) a b))

(def indexed-max-attains-spec
  {:name 'signed/indexed-max-from-attains
   :universes []
   :type
   (function/forall
    [['env environment-type] ['init signed] ['n nat]]
    (disjt (eqs (imax-from 'env 'init 'n) 'init)
           (existence (function/lam [['i nat]]
                                    (conj-t (strict-below 'i 'n) (eqs (imax-from 'env 'init 'n) (app 'env 'i)))))))
   :value
   (let [im (fn [k] (imax-from 'env 'init k))
         attained (fn [k] (existence (function/lam [['i nat]]
                                                   (conj-t (strict-below 'i k) (eqs (im k) (app 'env 'i))))))
         goal (fn [k] (disjt (eqs (im k) 'init) (attained k)))
         motive (function/lam [['k nat]] (goal 'k))
         base (left-disj (eqs (im nat-zero) 'init) (attained nat-zero) (refls 'init))
         stepfn
         (function/lam
          [['m nat] ['ih (goal 'm)]]
          (let [predB (function/lam [['i nat]] (conj-t (strict-below 'i (succ 'm)) (eqs (im (succ 'm)) (app 'env 'i))))
                predM (function/lam [['i nat]] (conj-t (strict-below 'i 'm) (eqs (im 'm) (app 'env 'i))))]
            (use-disj (eqs (im (succ 'm)) (im 'm)) (eqs (im (succ 'm)) (app 'env 'm)) (goal (succ 'm))
                      (max-lr (im 'm) (app 'env 'm))
                      ;; case A: im(succ m) = im m -> recurse on ih
                      (function/lam
                       [['hA (eqs (im (succ 'm)) (im 'm))]]
                       (use-disj (eqs (im 'm) 'init) (attained 'm) (goal (succ 'm))
                                 'ih
                                 ;; ih-left: im m = init
                                 (function/lam [['hL (eqs (im 'm) 'init)]]
                                               (left-disj (eqs (im (succ 'm)) 'init) (attained (succ 'm))
                                                          (trs (im (succ 'm)) (im 'm) 'init 'hA 'hL)))
                                 ;; ih-right: exists i<m, im m = env i
                                 (function/lam
                                  [['hR (attained 'm)]]
                                  (app 'hR (goal (succ 'm))
                                       (function/lam
                                        [['i nat] ['cj (conj-t (strict-below 'i 'm) (eqs (im 'm) (app 'env 'i)))]]
                                        (right-disj (eqs (im (succ 'm)) 'init) (attained (succ 'm))
                                                    (witness predB 'i
                                                             (conjoin (strict-below 'i (succ 'm)) (eqs (im (succ 'm)) (app 'env 'i))
                                                                      (sb-weaken 'i 'm (pleft (strict-below 'i 'm) (eqs (im 'm) (app 'env 'i)) 'cj))
                                                                      (trs (im (succ 'm)) (im 'm) (app 'env 'i)
                                                                           'hA
                                                                           (pright (strict-below 'i 'm) (eqs (im 'm) (app 'env 'i)) 'cj))))))))))
                      ;; case B: im(succ m) = env m -> witness m
                      (function/lam
                       [['hB (eqs (im (succ 'm)) (app 'env 'm))]]
                       (right-disj (eqs (im (succ 'm)) 'init) (attained (succ 'm))
                                   (witness predB 'm
                                            (conjoin (strict-below 'm (succ 'm)) (eqs (im (succ 'm)) (app 'env 'm))
                                                     (sb-self 'm) 'hB)))))))]
     (function/lam
      [['env environment-type] ['init signed] ['n nat]]
      (app (function/const* 'data/Nat.rec [prop-level]) motive base stepfn 'n)))})

(def theorem-specs [max-is-left-or-right-spec indexed-max-attains-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      imaxmod/extend-environment
      more/extend-environment
      (support/extend-with :signed-indexed-max-attains theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
