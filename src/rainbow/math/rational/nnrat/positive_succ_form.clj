(ns rainbow.math.rational.nnrat.positive-succ-form
  "A positive nnrat in make(succ p, q) form, so the reciprocal machinery
  (divide-self-positive / reciprocal-scale-cancel, which are stated for make(succ p, q))
  applies to it.

    nat/successor-of-predecessor : 1 <= n -> succ (predecessor n) = n
    nnrat/make-succ-of-positive-numerator :
        1 <= numerator c -> c ~ make (succ (predecessor (numerator c))) (denominator-predecessor c)

  The nnrat bridge is just: the cross-product of c and that make differ only by
  numerator c vs succ(pred(numerator c)), equal by the nat lemma. Axiom-free; additive."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.monus :as nnrat-monus]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eqn [x y] (function/equality tl nat x y))
(defn- sym-n [x y h] (app (function/const* 'equality/symmetric [tl]) nat x y h))
(defn- tr-n [x y z h1 h2] (app (function/const* 'equality/transitive [tl]) nat x y z h1 h2))
(defn- congr-n [ff x y h] (app (function/const* 'equality/congruent-function [tl tl]) nat nat ff x y h))
(defn- use-witness [pred goal ex handler] (app (function/const* 'proposition/use-witness [tl]) nat pred goal ex handler))
(def ^:private succ-fn (function/lam [['k nat]] (succ 'k)))
(def ^:private pred-fn (function/lam [['k nat]] (pred* 'k)))
;; nnrat
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- pair [num denpred] (app (function/const* 'data/pair [tl tl]) nat nat num denpred))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- denr [x] (app (function/const* 'nnrat/denominator []) x))
(defn- nnequiv [p q] (app (function/const* 'nnrat/equivalent []) p q))

;; 1 <= n  ->  succ (predecessor n) = n
(def successor-of-predecessor-spec
  {:name 'nat/successor-of-predecessor
   :universes []
   :type (function/forall [['n nat] ['h (nat-le (succ zero) 'n)]] (eqn (succ (pred* 'n)) 'n))
   :value
   (function/lam [['n nat] ['h (nat-le (succ zero) 'n)]]
                 (use-witness (function/lam [['d nat]] (eqn (nadd (succ zero) 'd) 'n))
                              (eqn (succ (pred* 'n)) 'n)
                              'h
                              (function/lam [['d nat] ['hd (eqn (nadd (succ zero) 'd) 'n)]]
                    ;; nadd (succ 0) d =def= succ d ; pred (succ d) =def= d
                                            (let [predeq (congr-n pred-fn 'n (nadd (succ zero) 'd) (sym-n (nadd (succ zero) 'd) 'n 'hd))]  ; pred n = pred(nadd(succ 0)d) =def= d
                                              (tr-n (succ (pred* 'n)) (succ 'd) 'n
                                                    (congr-n succ-fn (pred* 'n) 'd predeq)   ; succ(pred n) = succ d
                                                    'hd)))))})                                ; succ d =def= nadd(succ 0)d = n
(defn- succ-of-pred [n h] (app (function/const* 'nat/successor-of-predecessor []) n h))

;; 1 <= numerator c  ->  c ~ make (succ (predecessor (numerator c))) (denominator-predecessor c)
(def make-succ-of-positive-numerator-spec
  {:name 'nnrat/make-succ-of-positive-numerator
   :universes []
   :type (function/forall [['c nnrat] ['h (nat-le (succ zero) (numr 'c))]]
                          (nnequiv 'c (pair (succ (pred* (numr 'c))) (denpred 'c))))
   :value
   (function/lam [['c nnrat] ['h (nat-le (succ zero) (numr 'c))]]
     ;; nnequiv c (make ...) reduces to eq (num c * den c) (succ(pred(num c)) * den c)
     ;; [den(make ...) =def= den c since den-pred(make a b)=b]. Close by the nat lemma.
                 (let [dc (denr 'c)
                       numeq (succ-of-pred (numr 'c) 'h)]        ; succ(pred(num c)) = num c
                   (congr-n (function/lam [['t nat]] (nmul 't dc)) (numr 'c) (succ (pred* (numr 'c)))
                            (sym-n (succ (pred* (numr 'c))) (numr 'c) numeq))))})

(def theorem-specs [successor-of-predecessor-spec make-succ-of-positive-numerator-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.monus])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-positive-succ-form theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.positive-succ-form))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
