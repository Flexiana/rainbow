(ns rainbow.math.nat.extremal-index
  "LEAST AND GREATEST WITNESSES of a decidable predicate on 0..k, constructively (for the
  Floyd-Warshall invariant: the first and last intermediate visit of the new pivot).

     nat/bounded-search-decidable : (forall s, Q s \\/ not Q s) ->
                                    (exists s <= k, Q s) \\/ (forall s <= k, not Q s)
     nat/least-witness    : decidable Q -> (exists s <= k, Q s) ->
                            exists s, s <= k /\\ Q s /\\ forall s' < s, not Q s'
     nat/greatest-witness : decidable Q -> (exists s <= k, Q s) ->
                            exists s, s <= k /\\ Q s /\\ forall s', s < s' -> s' <= k -> not Q s'

  All three are by induction on k."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.nat.pigeonhole :as pigeonhole]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private pred-type (function/arrow nat 'Prop))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- falsity [] (function/const* 'proposition/falsity []))
(defn- not* [P] (function/arrow P (falsity)))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- exists-nat [pred] (proposition/existence type-level nat pred))
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))

(defn- le-of-below-succ [t k h] (@#'pigeonhole/le-of-below-succ t k h))
(defn- zero-of-le-zero [t h] (@#'pigeonhole/zero-of-le-zero t h))
(defn- below-zero-absurd [i hi P] (@#'pigeonhole/below-zero-absurd i hi P))

(defn- decidable [Q] (function/forall [['s nat]] (disj* (app Q 's) (not* (app Q 's)))))
(defn- some-below [Q k] (exists-nat (function/lam [['s nat]] (conj* (at-most 's k) (app Q 's)))))
(defn- none-below [Q k] (function/forall [['s nat] ['hs (at-most 's k)]] (not* (app Q 's))))
(defn- search-prop [Q k] (disj* (some-below Q k) (none-below Q k)))

(def search-spec
  {:name 'nat/bounded-search-decidable :universes []
   :type (function/forall [['Q pred-type] ['hd (decidable 'Q)] ['k nat]] (search-prop 'Q 'k))
   :value
   (function/lam
    [['Q pred-type] ['hd (decidable 'Q)] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (search-prop 'Q 'kk))
         (use-disj (app 'Q nat-zero) (not* (app 'Q nat-zero)) (search-prop 'Q nat-zero) (app 'hd nat-zero)
                   (function/lam [['h (app 'Q nat-zero)]]
                                 (left-disj (some-below 'Q nat-zero) (none-below 'Q nat-zero)
                                            (witness (function/lam [['s nat]] (conj* (at-most 's nat-zero) (app 'Q 's))) nat-zero
                                                     (conjoin (at-most nat-zero nat-zero) (app 'Q nat-zero) (at-most-refl nat-zero) 'h))))
                   (function/lam [['h (not* (app 'Q nat-zero))]]
                                 (right-disj (some-below 'Q nat-zero) (none-below 'Q nat-zero)
                                             (function/lam [['s nat] ['hs (at-most 's nat-zero)] ['hq (app 'Q 's)]]
                                                           (app 'h (subst-nat 's nat-zero (zero-of-le-zero 's 'hs) (function/lam [['z nat]] (app 'Q 'z)) 'hq))))))
         (function/lam
          [['k nat] ['ih (search-prop 'Q 'k)]]
          (let [k1 (succ 'k) goal (search-prop 'Q k1)
                P1 (function/lam [['s nat]] (conj* (at-most 's k1) (app 'Q 's)))
                P0 (function/lam [['s nat]] (conj* (at-most 's 'k) (app 'Q 's)))]
            (use-disj (some-below 'Q 'k) (none-below 'Q 'k) goal 'ih
                      (function/lam [['hs (some-below 'Q 'k)]]
                                    (left-disj (some-below 'Q k1) (none-below 'Q k1)
                                               (app 'hs (some-below 'Q k1)
                                                    (function/lam [['s nat] ['pf (app P0 's)]]
                                                                  (witness P1 's (conjoin (at-most 's k1) (app 'Q 's)
                                                                                          (amt 's 'k k1 (pleft (at-most 's 'k) (app 'Q 's) 'pf) (at-most-succ 'k))
                                                                                          (pright (at-most 's 'k) (app 'Q 's) 'pf)))))))
                      (function/lam
                       [['hn (none-below 'Q 'k)]]
                       (use-disj (app 'Q k1) (not* (app 'Q k1)) goal (app 'hd k1)
                                 (function/lam [['h (app 'Q k1)]]
                                               (left-disj (some-below 'Q k1) (none-below 'Q k1)
                                                          (witness P1 k1 (conjoin (at-most k1 k1) (app 'Q k1) (at-most-refl k1) 'h))))
                                 (function/lam [['h (not* (app 'Q k1))]]
                                               (right-disj (some-below 'Q k1) (none-below 'Q k1)
                                                           (function/lam [['s nat] ['hs (at-most 's k1)] ['hq (app 'Q 's)]]
                                                                         (use-disj (eq-nat 's k1) (strict-below 's k1) (falsity)
                                                                                   (app (function/const* 'nat/at-most-split []) 's k1 'hs)
                                                                                   (function/lam [['he (eq-nat 's k1)]] (app 'h (subst-nat 's k1 'he (function/lam [['z nat]] (app 'Q 'z)) 'hq)))
                                                                                   (function/lam [['hl (strict-below 's k1)]] (app 'hn 's (le-of-below-succ 's 'k 'hl) 'hq)))))))))))
         'k))})

;; ---------------------------------------------------------------------------------------------
(defn- least-body [Q k]
  (function/lam [['s nat]] (conj* (at-most 's k) (conj* (app Q 's) (function/forall [['s2 nat] ['hs2 (strict-below 's2 's)]] (not* (app Q 's2)))))))
(defn- least-claim [Q k] (function/arrow (some-below Q k) (exists-nat (least-body Q k))))

(def least-spec
  {:name 'nat/least-witness :universes []
   :type (function/forall [['Q pred-type] ['hd (decidable 'Q)] ['k nat]] (least-claim 'Q 'k))
   :value
   (function/lam
    [['Q pred-type] ['hd (decidable 'Q)] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (least-claim 'Q 'kk))
         ;; k = 0: the witness is 0, and nothing is below 0
         (function/lam
          [['hex (some-below 'Q nat-zero)]]
          (app 'hex (exists-nat (least-body 'Q nat-zero))
               (function/lam [['s nat] ['pf (conj* (at-most 's nat-zero) (app 'Q 's))]]
                             (let [s0 (zero-of-le-zero 's (pleft (at-most 's nat-zero) (app 'Q 's) 'pf))
                                   q0 (subst-nat 's nat-zero s0 (function/lam [['z nat]] (app 'Q 'z)) (pright (at-most 's nat-zero) (app 'Q 's) 'pf))]
                               (witness (least-body 'Q nat-zero) nat-zero
                                        (conjoin (at-most nat-zero nat-zero) (conj* (app 'Q nat-zero) (function/forall [['s2 nat] ['hs2 (strict-below 's2 nat-zero)]] (not* (app 'Q 's2))))
                                                 (at-most-refl nat-zero)
                                                 (conjoin (app 'Q nat-zero) (function/forall [['s2 nat] ['hs2 (strict-below 's2 nat-zero)]] (not* (app 'Q 's2))) q0
                                                          (function/lam [['s2 nat] ['hs2 (strict-below 's2 nat-zero)]] (below-zero-absurd 's2 'hs2 (not* (app 'Q 's2)))))))))))
         (function/lam
          [['k nat] ['ih (least-claim 'Q 'k)] ['hex (some-below 'Q (succ 'k))]]
          (let [k1 (succ 'k) goal (exists-nat (least-body 'Q k1))]
            (use-disj (some-below 'Q 'k) (none-below 'Q 'k) goal (app (function/const* 'nat/bounded-search-decidable []) 'Q 'hd 'k)
                      ;; a witness <= k: its least one also works for k + 1
                      (function/lam
                       [['hs (some-below 'Q 'k)]]
                       (app (app 'ih 'hs) goal
                            (function/lam [['s nat] ['pf (app (least-body 'Q 'k) 's)]]
                                          (let [rest (conj* (app 'Q 's) (function/forall [['s2 nat] ['hs2 (strict-below 's2 's)]] (not* (app 'Q 's2))))]
                                            (witness (least-body 'Q k1) 's
                                                     (conjoin (at-most 's k1) rest
                                                              (amt 's 'k k1 (pleft (at-most 's 'k) rest 'pf) (at-most-succ 'k))
                                                              (pright (at-most 's 'k) rest 'pf)))))))
                      ;; none <= k: the witness is k + 1, and it is least
                      (function/lam
                       [['hn (none-below 'Q 'k)]]
                       (app 'hex goal
                            (function/lam [['s nat] ['pf (conj* (at-most 's k1) (app 'Q 's))]]
                                          (let [hs-le (pleft (at-most 's k1) (app 'Q 's) 'pf) hq (pright (at-most 's k1) (app 'Q 's) 'pf)
                                                rest (conj* (app 'Q 's) (function/forall [['s2 nat] ['hs2 (strict-below 's2 's)]] (not* (app 'Q 's2))))]
                                            (witness (least-body 'Q k1) 's
                                                     (conjoin (at-most 's k1) rest hs-le
                                                              (conjoin (app 'Q 's) (function/forall [['s2 nat] ['hs2 (strict-below 's2 's)]] (not* (app 'Q 's2))) hq
                                                                       (function/lam [['s2 nat] ['hs2 (strict-below 's2 's)]]
                                                                                     (app 'hn 's2 (le-of-below-succ 's2 'k (amt (succ 's2) 's k1 'hs2 hs-le))))))))))))))
         'k))})

;; ---------------------------------------------------------------------------------------------
(defn- greatest-body [Q k]
  (function/lam [['s nat]] (conj* (at-most 's k) (conj* (app Q 's) (function/forall [['s2 nat] ['hs2 (strict-below 's 's2)] ['hk2 (at-most 's2 k)]] (not* (app Q 's2)))))))
(defn- greatest-claim [Q k] (function/arrow (some-below Q k) (exists-nat (greatest-body Q k))))

(def greatest-spec
  {:name 'nat/greatest-witness :universes []
   :type (function/forall [['Q pred-type] ['hd (decidable 'Q)] ['k nat]] (greatest-claim 'Q 'k))
   :value
   (function/lam
    [['Q pred-type] ['hd (decidable 'Q)] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (greatest-claim 'Q 'kk))
         ;; k = 0: the witness is 0, and nothing lies in (0, 0]
         (function/lam
          [['hex (some-below 'Q nat-zero)]]
          (app 'hex (exists-nat (greatest-body 'Q nat-zero))
               (function/lam [['s nat] ['pf (conj* (at-most 's nat-zero) (app 'Q 's))]]
                             (let [s0 (zero-of-le-zero 's (pleft (at-most 's nat-zero) (app 'Q 's) 'pf))
                                   q0 (subst-nat 's nat-zero s0 (function/lam [['z nat]] (app 'Q 'z)) (pright (at-most 's nat-zero) (app 'Q 's) 'pf))
                                   above (function/forall [['s2 nat] ['hs2 (strict-below nat-zero 's2)] ['hk2 (at-most 's2 nat-zero)]] (not* (app 'Q 's2)))]
                               (witness (greatest-body 'Q nat-zero) nat-zero
                                        (conjoin (at-most nat-zero nat-zero) (conj* (app 'Q nat-zero) above) (at-most-refl nat-zero)
                                                 (conjoin (app 'Q nat-zero) above q0
                                                          (function/lam [['s2 nat] ['hs2 (strict-below nat-zero 's2)] ['hk2 (at-most 's2 nat-zero)]]
                                                                        (below-zero-absurd nat-zero (subst-nat 's2 nat-zero (zero-of-le-zero 's2 'hk2) (function/lam [['z nat]] (strict-below nat-zero 'z)) 'hs2)
                                                                                           (not* (app 'Q 's2)))))))))))
         (function/lam
          [['k nat] ['ih (greatest-claim 'Q 'k)] ['hex (some-below 'Q (succ 'k))]]
          (let [k1 (succ 'k) goal (exists-nat (greatest-body 'Q k1))]
            (use-disj (app 'Q k1) (not* (app 'Q k1)) goal (app 'hd k1)
                      ;; Q (k + 1): it is the greatest
                      (function/lam
                       [['h (app 'Q k1)]]
                       (let [above (function/forall [['s2 nat] ['hs2 (strict-below k1 's2)] ['hk2 (at-most 's2 k1)]] (not* (app 'Q 's2)))]
                         (witness (greatest-body 'Q k1) k1
                                  (conjoin (at-most k1 k1) (conj* (app 'Q k1) above) (at-most-refl k1)
                                           (conjoin (app 'Q k1) above 'h
                                                    (function/lam [['s2 nat] ['hs2 (strict-below k1 's2)] ['hk2 (at-most 's2 k1)]]
                                                                  (explode (not* (app 'Q 's2)) (app (function/const* 'nat/not-strictly-below-self []) k1 (amt (succ k1) 's2 k1 'hs2 'hk2)))))))))
                      ;; not Q (k + 1): the witness is <= k; take the greatest there and extend
                      (function/lam
                       [['h (not* (app 'Q k1))]]
                       (let [below-k (app 'hex (some-below 'Q 'k)
                                          (function/lam [['s nat] ['pf (conj* (at-most 's k1) (app 'Q 's))]]
                                                        (let [hs-le (pleft (at-most 's k1) (app 'Q 's) 'pf) hq (pright (at-most 's k1) (app 'Q 's) 'pf)]
                                                          (use-disj (eq-nat 's k1) (strict-below 's k1) (some-below 'Q 'k)
                                                                    (app (function/const* 'nat/at-most-split []) 's k1 hs-le)
                                                                    (function/lam [['he (eq-nat 's k1)]] (explode (some-below 'Q 'k) (app 'h (subst-nat 's k1 'he (function/lam [['z nat]] (app 'Q 'z)) hq))))
                                                                    (function/lam [['hl (strict-below 's k1)]]
                                                                                  (witness (function/lam [['s3 nat]] (conj* (at-most 's3 'k) (app 'Q 's3))) 's
                                                                                           (conjoin (at-most 's 'k) (app 'Q 's) (le-of-below-succ 's 'k 'hl) hq)))))))]
                         (app (app 'ih below-k) goal
                              (function/lam
                               [['s nat] ['pf (app (greatest-body 'Q 'k) 's)]]
                               (let [above-k (function/forall [['s2 nat] ['hs2 (strict-below 's 's2)] ['hk2 (at-most 's2 'k)]] (not* (app 'Q 's2)))
                                     rest (conj* (app 'Q 's) above-k)
                                     hsk (pleft (at-most 's 'k) rest 'pf)
                                     hq (pleft (app 'Q 's) above-k (pright (at-most 's 'k) rest 'pf))
                                     hab (pright (app 'Q 's) above-k (pright (at-most 's 'k) rest 'pf))
                                     above-k1 (function/forall [['s2 nat] ['hs2 (strict-below 's 's2)] ['hk2 (at-most 's2 k1)]] (not* (app 'Q 's2)))]
                                 (witness (greatest-body 'Q k1) 's
                                          (conjoin (at-most 's k1) (conj* (app 'Q 's) above-k1) (amt 's 'k k1 hsk (at-most-succ 'k))
                                                   (conjoin (app 'Q 's) above-k1 hq
                                                            (function/lam
                                                             [['s2 nat] ['hs2 (strict-below 's 's2)] ['hk2 (at-most 's2 k1)]]
                                                             (use-disj (eq-nat 's2 k1) (strict-below 's2 k1) (not* (app 'Q 's2))
                                                                       (app (function/const* 'nat/at-most-split []) 's2 k1 'hk2)
                                                                       (function/lam [['he (eq-nat 's2 k1)]] (subst-nat k1 's2 (nat-sym 's2 k1 'he) (function/lam [['z nat]] (not* (app 'Q 'z))) 'h))
                                                                       (function/lam [['hl (strict-below 's2 k1)]] (app hab 's2 'hs2 (le-of-below-succ 's2 'k 'hl))))))))))))))))
         'k))})

(def theorem-specs [search-spec least-spec greatest-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      pigeonhole/extend-environment
      (support/extend-with :nat-extremal-index theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
