(ns rainbow.math.rational.signed.convergence
  "Real-analysis roadmap step 5: the epsilon-N convergence predicate over signed-rational
  sequences, and the SQUEEZE THEOREM -- the first genuinely-frontier analysis result and
  the checkpoint that the epsilon-N machinery goes through in this kernel.

    analysis/close L eps x   :=  (L - eps <= x)  AND  (x <= L + eps)      (order band)
    analysis/converges s L M :=  forall eps n, M eps <= n  ->  close L eps (s n)

    analysis/squeeze : a <= s <= b pointwise, a -> L, b -> L  ==>  s -> L
      with combined modulus  M eps = Ma eps + Mb eps.

  The squeeze needs no new signed arithmetic -- only the signed order transitivity from
  step 4: for n >= Ma+Mb we get n >= Ma and n >= Mb (nat le-add via witnesses), read off
  L-eps <= a(n) and b(n) <= L+eps from the two convergences (conjunction projections),
  and chain L-eps <= a(n) <= s(n) and s(n) <= b(n) <= L+eps through
  signed/at-most-transitive.

  Native and axiom-free; chains rainbow.math.rational.signed.order-transitivity on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.signed.order-transitivity :as st]))

(def type-level [:succ [:zero]])
(def signed (function/const* 'signed/SignedRational []))
(def nat (function/const* 'data/Nat []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))

(defn- app [f & args] (apply function/app f args))
(defn- ssub [a b] (function/app (function/const* 'signed/subtract []) a b))
(defn- sadd [a b] (function/app (function/const* 'signed/add []) a b))
(defn- sle [a b] (function/app (function/const* 'signed/at-most []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- add-comm-nat [a b]
  (function/app (function/const* 'nat/add-commutative []) a b))
(defn- witness-nat [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))
(defn- nat-transitive [l m r p q]
  (function/app (function/const* 'nat/at-most-transitive []) l m r p q))
(defn- signed-transitive [l m r p q]
  (function/app (function/const* 'signed/at-most-transitive []) l m r p q))
(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r pl pr] (function/app (function/const* 'proposition/conjoin []) l r pl pr))
(defn- prop-left [l r both] (function/app (function/const* 'proposition/left []) l r both))
(defn- prop-right [l r both] (function/app (function/const* 'proposition/right []) l r both))
(defn- the-close [L eps x] (function/app (function/const* 'analysis/close []) L eps x))
(defn- the-converges [s L M] (function/app (function/const* 'analysis/converges []) s L M))

;; ---- definitions ------------------------------------------------------------
(def close-spec
  {:name 'analysis/close :kind :definition :universes []
   :type (function/arrow signed signed signed 'Prop)
   :value (function/lam [['L signed] ['eps signed] ['x signed]]
                        (conjunction (sle (ssub 'L 'eps) 'x) (sle 'x (sadd 'L 'eps))))})

(def converges-spec
  {:name 'analysis/converges :kind :definition :universes []
   :type (function/arrow sig-seq signed modulus 'Prop)
   :value (function/lam [['s sig-seq] ['L signed] ['M modulus]]
                        (function/forall
                         [['eps signed] ['n nat]]
                         (function/arrow (nat-at-most (app 'M 'eps) 'n)
                                         (the-close 'L 'eps (app 's 'n)))))})

;; ---- squeeze theorem --------------------------------------------------------
(def squeeze-spec
  {:name 'analysis/squeeze :universes []
   :type (function/forall
          [['a sig-seq] ['b sig-seq] ['s sig-seq] ['L signed]
           ['Ma modulus] ['Mb modulus]
           ['ha-s (function/forall [['n nat]] (sle (app 'a 'n) (app 's 'n)))]
           ['hs-b (function/forall [['n nat]] (sle (app 's 'n) (app 'b 'n)))]
           ['ca (the-converges 'a 'L 'Ma)]
           ['cb (the-converges 'b 'L 'Mb)]]
          (the-converges 's 'L (function/lam [['eps signed]] (nadd (app 'Ma 'eps) (app 'Mb 'eps)))))
   :value
   (function/lam
    [['a sig-seq] ['b sig-seq] ['s sig-seq] ['L signed]
     ['Ma modulus] ['Mb modulus]
     ['ha-s (function/forall [['n nat]] (sle (app 'a 'n) (app 's 'n)))]
     ['hs-b (function/forall [['n nat]] (sle (app 's 'n) (app 'b 'n)))]
     ['ca (the-converges 'a 'L 'Ma)]
     ['cb (the-converges 'b 'L 'Mb)]]
    (function/lam
     [['eps signed] ['n nat]
      ['hn (nat-at-most (nadd (app 'Ma 'eps) (app 'Mb 'eps)) 'n)]]
     (let [ma (app 'Ma 'eps) mb (app 'Mb 'eps) sum (nadd ma mb)
           an (app 'a 'n) bn (app 'b 'n) sn (app 's 'n)
           lo (ssub 'L 'eps) hi (sadd 'L 'eps)
           ;; ma <= sum (witness mb), mb <= sum (witness ma via add-commutative)
           ma<=sum (witness-nat (function/lam [['k nat]] (eq-nat (nadd ma 'k) sum))
                                mb (reflexive-nat sum))
           mb<=sum (witness-nat (function/lam [['k nat]] (eq-nat (nadd mb 'k) sum))
                                ma (add-comm-nat mb ma))
           ma<=n (nat-transitive ma sum 'n ma<=sum 'hn)
           mb<=n (nat-transitive mb sum 'n mb<=sum 'hn)
           ;; read off the bands from the two convergences
           close-a (app 'ca 'eps 'n ma<=n)   ; close L eps (a n) = (lo<=an) AND (an<=hi)
           close-b (app 'cb 'eps 'n mb<=n)    ; close L eps (b n) = (lo<=bn) AND (bn<=hi)
           lo<=an (prop-left (sle lo an) (sle an hi) close-a)
           bn<=hi (prop-right (sle lo bn) (sle bn hi) close-b)
           ;; chain lo <= a n <= s n  and  s n <= b n <= hi
           lo<=sn (signed-transitive lo an sn lo<=an (app 'ha-s 'n))
           sn<=hi (signed-transitive sn bn hi (app 'hs-b 'n) bn<=hi)]
       (conjoin (sle lo sn) (sle sn hi) lo<=sn sn<=hi))))})

(def definition-specs [close-spec converges-spec])
(def theorem-specs [squeeze-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.order-transitivity])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-convergence (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.convergence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
