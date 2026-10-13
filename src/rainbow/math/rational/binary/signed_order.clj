(ns rainbow.math.rational.binary.signed-order
  "The SIGNED bridge: the checker's actual hot decision `signed/decide-at-most` on the
  Bin layer, proved to agree with -- and to entail the soundness of -- the trusted
  signed order.

  `signed/decide-at-most` is `reducible` to the audit decision on two nnrat SUMS of
  the signed parts:
    signed/decide-at-most a b = audit/decide-nnrat-at-most (pos a + neg b) (pos b + neg a)
  and `signed/at-most a b` reduces to `nnrat/at-most` of the same two sums. So the
  signed-level facts are thin instances of the brick-5b nnrat-level lemmas with
  l := (pos a + neg b) and r := (pos b + neg a): no new arithmetic, the defeq of the
  reducible signed definitions does the work.

  This is what a Bin-native checker (5c) invokes directly:
    bin/decide-signed-sound         : decide=true  -> signed/at-most a b
    bin/decide-signed-false-reverse : decide=false -> signed/at-most b a
    bin/decide-signed-matches       : the Bin decision equals signed/decide-at-most a b
  each taking Bin representations of the two cross-SUMS' num/den.

  And the capstone bin/decide-signed-sound-from-parts CONSTRUCTS those cross-sums on
  Bin from the four signed parts (num/den of pos a, neg a, pos b, neg b) via
  bin-add/bin-multiply -- using the brick-5b construction theorems bin/to-nat-rat-add-num
  and -den (nnrat/add's num/den reduce definitionally to the cross forms, the
  make-predecessor convention cancelling) -- so decide=true on the fully-Bin decision
  entails signed/at-most a b with NO unary Nat of the operands' magnitude ever built.
  That is the single lemma a Bin-native checker (5c) invokes.

  ADDITIVE: installs into a bin-rational-order-extended environment; trusted checker
  untouched. Reuses bin/decide-rat-matches-audit, bin/decide-rat-sound,
  bin/decide-rat-false-reverse, bin/to-nat-rat-add-num, bin/to-nat-rat-add-den."
  (:require [rainbow.module :as module]
            [rainbow.kernel :as kernel]
            [rainbow.elaborate :as elaborate]
            [rainbow.term :as term]
            [rainbow.math.logic.function :as function]))

(def ^:private type-level [:succ [:zero]])
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private Bin (function/const* 'data/Bin []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))

(defn- pos [v] (function/app (function/const* 'signed/positive []) v))
(defn- neg [v] (function/app (function/const* 'signed/negative []) v))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- forward [a b] (radd (pos a) (neg b)))      ; the nnrat 'l' signed order unfolds to
(defn- backward [a b] (radd (pos b) (neg a)))     ; the nnrat 'r'
(defn- sle [a b] (function/app (function/const* 'signed/at-most []) a b))
(defn- decide-signed [a b] (function/app (function/const* 'signed/decide-at-most []) a b))
(defn- tn [b] (function/app (function/const* 'bin/to-nat []) b))
(defn- numr [x] (function/app (function/const* 'nnrat/numerator []) x))
(defn- denr [x] (function/app (function/const* 'nnrat/denominator []) x))
(defn- eq-bool [x y] (function/equality type-level bool x y))
(defn- eq-nat [x y] (function/equality type-level (function/const* 'data/Nat []) x y))
(defn- decide-rat [nf df nb db] (function/app (function/const* 'bin/decide-rat-at-most []) nf df nb db))

;; the four hypotheses: the Bin fields represent the num/den of the two cross-SUMS.
(defn- represents-hyps [a b]
  [['hnf (eq-nat (tn 'nf) (numr (forward a b)))] ['hdf (eq-nat (tn 'df) (denr (forward a b)))]
   ['hnb (eq-nat (tn 'nb) (numr (backward a b)))] ['hdb (eq-nat (tn 'db) (denr (backward a b)))]])

(defn- signed-binders [a b concl]
  (function/forall
   (into [['a signed] ['b signed] ['nf Bin] ['df Bin] ['nb Bin] ['db Bin]] (represents-hyps a b))
   concl))

;; bin/decide-signed-matches : the Bin decision equals signed/decide-at-most a b
;; (an instance of bin/decide-rat-matches-audit at l=forward, r=backward; the audit
;; decision on those sums is definitionally signed/decide-at-most a b).
(def decide-signed-matches-spec
  {:name 'bin/decide-signed-matches
   :universes []
   :type (signed-binders 'a 'b (eq-bool (decide-rat 'nf 'df 'nb 'db) (decide-signed 'a 'b)))
   :value
   (function/lam
    (into [['a signed] ['b signed] ['nf Bin] ['df Bin] ['nb Bin] ['db Bin]] (represents-hyps 'a 'b))
    (function/app (function/const* 'bin/decide-rat-matches-audit [])
                  (forward 'a 'b) (backward 'a 'b) 'nf 'df 'nb 'db 'hnf 'hdf 'hnb 'hdb))})

;; bin/decide-signed-sound : decide=true -> signed/at-most a b
;; (instance of bin/decide-rat-sound; nnrat/at-most(forward)(backward) is defeq sle a b).
(def decide-signed-sound-spec
  {:name 'bin/decide-signed-sound
   :universes []
   :type (signed-binders 'a 'b
                         (function/forall [['h (eq-bool (decide-rat 'nf 'df 'nb 'db) true-value)]] (sle 'a 'b)))
   :value
   (function/lam
    (into [['a signed] ['b signed] ['nf Bin] ['df Bin] ['nb Bin] ['db Bin]] (represents-hyps 'a 'b))
    (function/lam [['h (eq-bool (decide-rat 'nf 'df 'nb 'db) true-value)]]
                  (function/app (function/const* 'bin/decide-rat-sound [])
                                (forward 'a 'b) (backward 'a 'b) 'nf 'df 'nb 'db 'hnf 'hdf 'hnb 'hdb 'h)))})

;; bin/decide-signed-false-reverse : decide=false -> signed/at-most b a
;; (instance of bin/decide-rat-false-reverse; nnrat/at-most(backward a b)(forward a b)
;; is defeq sle b a, since forward b a = backward a b and backward b a = forward a b).
(def decide-signed-false-reverse-spec
  {:name 'bin/decide-signed-false-reverse
   :universes []
   :type (signed-binders 'a 'b
                         (function/forall [['h (eq-bool (decide-rat 'nf 'df 'nb 'db) false-value)]] (sle 'b 'a)))
   :value
   (function/lam
    (into [['a signed] ['b signed] ['nf Bin] ['df Bin] ['nb Bin] ['db Bin]] (represents-hyps 'a 'b))
    (function/lam [['h (eq-bool (decide-rat 'nf 'df 'nb 'db) false-value)]]
                  (function/app (function/const* 'bin/decide-rat-false-reverse [])
                                (forward 'a 'b) (backward 'a 'b) 'nf 'df 'nb 'db 'hnf 'hdf 'hnb 'hdb 'h)))})

;; ---- capstone: fully Bin-native signed soundness FROM THE PARTS ----
;; The one lemma 5c invokes. Takes Bin representations of the num/den of all four
;; signed parts (pos a, neg a, pos b, neg b), builds the two cross-SUM Bin values via
;; bin-add/bin-multiply (the brick-5b construction theorems relate them to
;; num/den(forward/backward)), runs the fully-Bin decision, and concludes the trusted
;; signed order. No unary Nat of the operands' magnitude is ever materialised.
(defn- bmul [a b] (function/app (function/const* 'bin/bin-multiply []) a b))
(defn- badd [a b] (function/app (function/const* 'bin/bin-add []) a b))
(defn- add-num [p q np dp nq dq hnp hdp hnq hdq]
  (function/app (function/const* 'bin/to-nat-rat-add-num []) p q np dp nq dq hnp hdp hnq hdq))
(defn- add-den [p q dp dq hdp hdq]
  (function/app (function/const* 'bin/to-nat-rat-add-den []) p q dp dq hdp hdq))

;; forward = pos a + neg b : num = bin-add(pna*ndb)(nnb*pda), den = pda*ndb
;; backward = pos b + neg a : num = bin-add(pnb*nda)(nna*pdb), den = pdb*nda
(defn- fwd-num [] (badd (bmul 'pna 'ndb) (bmul 'nnb 'pda)))
(defn- fwd-den [] (bmul 'pda 'ndb))
(defn- bwd-num [] (badd (bmul 'pnb 'nda) (bmul 'nna 'pdb)))
(defn- bwd-den [] (bmul 'pdb 'nda))

(def ^:private part-binders
  [['a signed] ['b signed]
   ['pna Bin] ['pda Bin] ['nna Bin] ['nda Bin]   ; num/den of pos a, neg a
   ['pnb Bin] ['pdb Bin] ['nnb Bin] ['ndb Bin]   ; num/den of pos b, neg b
   ['hpna (eq-nat (tn 'pna) (numr (pos 'a)))] ['hpda (eq-nat (tn 'pda) (denr (pos 'a)))]
   ['hnna (eq-nat (tn 'nna) (numr (neg 'a)))] ['hnda (eq-nat (tn 'nda) (denr (neg 'a)))]
   ['hpnb (eq-nat (tn 'pnb) (numr (pos 'b)))] ['hpdb (eq-nat (tn 'pdb) (denr (pos 'b)))]
   ['hnnb (eq-nat (tn 'nnb) (numr (neg 'b)))] ['hndb (eq-nat (tn 'ndb) (denr (neg 'b)))]])

(def decide-signed-sound-from-parts-spec
  {:name 'bin/decide-signed-sound-from-parts
   :universes []
   :type (function/forall
          (conj part-binders
                ['h (eq-bool (decide-rat (fwd-num) (fwd-den) (bwd-num) (bwd-den)) true-value)])
          (sle 'a 'b))
   :value
   (function/lam
    (conj part-binders
          ['h (eq-bool (decide-rat (fwd-num) (fwd-den) (bwd-num) (bwd-den)) true-value)])
    (let [hnf (add-num (pos 'a) (neg 'b) 'pna 'pda 'nnb 'ndb 'hpna 'hpda 'hnnb 'hndb)
          hdf (add-den (pos 'a) (neg 'b) 'pda 'ndb 'hpda 'hndb)
          hnb (add-num (pos 'b) (neg 'a) 'pnb 'pdb 'nna 'nda 'hpnb 'hpdb 'hnna 'hnda)
          hdb (add-den (pos 'b) (neg 'a) 'pdb 'nda 'hpdb 'hnda)]
      (function/app (function/const* 'bin/decide-signed-sound [])
                    'a 'b (fwd-num) (fwd-den) (bwd-num) (bwd-den)
                    hnf hdf hnb hdb 'h)))})

(def definition-specs
  [decide-signed-matches-spec decide-signed-sound-spec decide-signed-false-reverse-spec
   decide-signed-sound-from-parts-spec])

(defn- add-definition [environment {:keys [name universes type value]}]
  (let [ct (elaborate/core-expression environment type)
        cv (elaborate/core-expression environment value)]
    (when-not (= :elaborated (:status ct))
      (throw (ex-info "bin-signed type failed elaboration"
                      {:error/category :bin-signed/elaboration-failed :name name :result ct})))
    (when-not (= :elaborated (:status cv))
      (throw (ex-info "bin-signed value failed elaboration"
                      {:error/category :bin-signed/elaboration-failed :name name :result cv})))
    (let [result (kernel/add-declaration
                  environment
                  {:rainbow/kind :definition
                   :rainbow/aliases #{name}
                   :rainbow/universes universes
                   :rainbow/type (:term ct)
                   :rainbow/value (:term cv)
                   :rainbow/transparency :reducible
                   :rainbow/dependencies (into (term/constants (:term ct)) (term/constants (:term cv)))
                   :rainbow/provenance {:origin :native :producer :bin-signed-order}
                   :rainbow/schema-version 1})]
      (when-not (= :accepted (:status result))
        (throw (ex-info "bin-signed definition rejected"
                        {:error/category :bin-signed/definition-rejected :name name :result result})))
      (:environment result))))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-definition checked-environment definition-specs))

(defn extend-environment
  "Install the Bin signed-order bridge. Requires signed/decide-at-most etc. from
  rainbow.math.rational.signed.decide-order AND the brick-5b lemmas: chain
    base -> signed-decide-order -> data.binary -> bin-rational-order -> bin-signed-order.
  Additive; trusted checker untouched." [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.binary.signed-order))
(defn block-aliases []
  '#{bin/decide-signed-matches bin/decide-signed-sound bin/decide-signed-false-reverse
     bin/decide-signed-sound-from-parts})
