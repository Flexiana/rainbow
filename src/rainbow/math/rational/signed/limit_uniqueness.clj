(ns rainbow.math.rational.signed.limit-uniqueness
  "Uniqueness of limits for the signed-rational epsilon-N convergence predicate.

  The reusable Archimedean lemma says that signed rationals lying in every positive
  reciprocal band are equivalent.  It reduces the two sides of each signed band to
  nnrat bounds and applies nnrat/at-most-of-all-plus-reciprocal in both directions.

  For limit uniqueness, at reciprocal radius r the first convergence supplies an
  r-band around L.  The second convergence is instantiated at signed zero, making the
  common sequence term order-equivalent to L'.  Transitivity therefore puts L' in the
  r-band around L, and the signed Archimedean lemma finishes the proof.

  Native, axiom-free, and built on the D63 signed convergence/order and nnrat
  Archimedean toolkits."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.archimedean :as arch]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.signed.order-respects :as respects]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))
(def zero-nat (function/const* 'data/zero []))
(def one-nat (function/app (function/const* 'data/succ []) zero-nat))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- succ [v] (app (function/const* 'data/succ []) v))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- make [n dp] (app (function/const* 'nnrat/make []) n dp))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- rat-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- rat-at-most [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- num [v] (app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))

(defn- reflexive-nat [v]
  (app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- symmetric-nat [a b p]
  (app (function/const* 'equality/symmetric [type-level]) nat a b p))
(defn- transitive-nat [a b c p q]
  (app (function/const* 'equality/transitive [type-level]) nat a b c p q))
(defn- congruent-nat [mapping a b p]
  (app (function/const* 'equality/congruent-function [type-level type-level])
       nat nat mapping a b p))
(defn- add-assoc-nat [a b c]
  (app (function/const* 'nat/add-associative []) a b c))
(defn- add-zero-right-nat [v]
  (app (function/const* 'algebra/nat-add-zero-right []) v))
(defn- add-left-cancel-nat [prefix a b p]
  (app (function/const* 'nat/add-left-cancel []) prefix a b p))
(defn- sum-zero-left-nat [a b p]
  (app (function/const* 'nat/sum-zero-left []) a b p))
(defn- use-witness-nat [pred goal exists handler]
  (app (function/const* 'proposition/use-witness [type-level])
       nat pred goal exists handler))
(defn- witness-nat [pred value proof]
  (app (function/const* 'proposition/witness [type-level])
       nat pred value proof))

(defn- rat-refl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b p]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b p))
(defn- rat-trans [a b c p q]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c p q))
(defn- rat-add-respects [a ah b bh pa pb]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh pa pb))
(defn- rat-add-assoc [a b c]
  (app (function/const* 'nnrat/add-associative []) a b c))
(defn- rat-add-comm [a b]
  (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-add-zero-right [v]
  (app (function/const* 'nnrat/add-zero-right []) v))
(defn- rat-at-most-respects [a ah b bh pa pb ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh pa pb ordered))
(defn- rat-to-cross [a b ordered]
  (app (function/const* 'nnrat/at-most-to-cross []) a b ordered))
(defn- rat-arch [a b bounded]
  (app (function/const* 'nnrat/at-most-of-all-plus-reciprocal [])
       a b bounded))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-trans [a b c p q]
  (app (function/const* 'signed/at-most-transitive []) a b c p q))
(defn- signed-at-most-respects [a ah b bh pa pb ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh pa pb ordered))
(defn- signed-antisym [a b ab ba]
  (app (function/const* 'signed/at-most-antisymmetric []) a b ab ba))

(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))

;; a<=b and b<=a imply a=b for the witness-based natural order.  Keeping this as
;; a proof-term constructor avoids adding an unrelated public declaration.
(defn- nat-antisymmetric [a b ab ba]
  (use-witness-nat
   (function/lam [['d nat]] (eq-nat (nadd a 'd) b))
   (eq-nat a b)
   ab
   (function/lam
    [['d nat] ['ad-eq-b (eq-nat (nadd a 'd) b)]]
    (use-witness-nat
     (function/lam [['e nat]] (eq-nat (nadd b 'e) a))
     (eq-nat a b)
     ba
     (function/lam
      [['e nat] ['be-eq-a (eq-nat (nadd b 'e) a)]]
      (let [ade-eq-be
            (congruent-nat (function/lam [['v nat]] (nadd 'v 'e))
                           (nadd a 'd) b 'ad-eq-b)
            ade-eq-a
            (transitive-nat (nadd (nadd a 'd) 'e) (nadd b 'e) a
                            ade-eq-be 'be-eq-a)
            ade-normal
            (transitive-nat
             (nadd a (nadd 'd 'e)) (nadd (nadd a 'd) 'e) a
             (symmetric-nat (nadd (nadd a 'd) 'e) (nadd a (nadd 'd 'e))
                            (add-assoc-nat a 'd 'e))
             ade-eq-a)
            ade-to-zero
            (transitive-nat
             (nadd a (nadd 'd 'e)) a (nadd a zero-nat)
             ade-normal
             (symmetric-nat (nadd a zero-nat) a (add-zero-right-nat a)))
            de-eq-zero (add-left-cancel-nat a (nadd 'd 'e) zero-nat ade-to-zero)
            d-eq-zero (sum-zero-left-nat 'd 'e de-eq-zero)
            ad-eq-a0
            (congruent-nat (function/lam [['v nat]] (nadd a 'v))
                           'd zero-nat d-eq-zero)
            a-eq-ad
            (transitive-nat
             a (nadd a zero-nat) (nadd a 'd)
             (symmetric-nat (nadd a zero-nat) a (add-zero-right-nat a))
             (symmetric-nat (nadd a 'd) (nadd a zero-nat) ad-eq-a0))]
        (transitive-nat a (nadd a 'd) b a-eq-ad 'ad-eq-b)))))))

;; (a+b)+c ~ (a+c)+b, assembled from the installed nnrat laws.
(defn- rat-reorder-three [a b c]
  (let [start (radd (radd a b) c)
        first (radd a (radd b c))
        second (radd a (radd c b))
        finish (radd (radd a c) b)]
    (rat-trans
     start first finish
     (rat-add-assoc a b c)
     (rat-trans
      first second finish
      (rat-add-respects a a (radd b c) (radd c b)
                        (rat-refl a) (rat-add-comm b c))
      (rat-sym finish second (rat-add-assoc a c b))))))

;; ---- signed additive identity ----------------------------------------------
(def signed-add-zero-right-spec
  {:name 'signed/add-zero-right :universes []
   :type (function/forall
          [['value signed]]
          (seq-equiv (sadd 'value signed-zero) 'value))
   :value
   (function/lam
    [['value signed]]
    (let [P (pos 'value) N (neg 'value)
          start (radd (radd P nnrat-zero) N)
          middle (radd P N)
          finish (radd P (radd N nnrat-zero))
          start-middle
          (rat-add-respects (radd P nnrat-zero) P N N
                            (rat-add-zero-right P) (rat-refl N))
          finish-middle
          (rat-add-respects P P (radd N nnrat-zero) N
                            (rat-refl P) (rat-add-zero-right N))]
      (rat-trans start middle finish
                 start-middle (rat-sym finish middle finish-middle))))})

;; ---- antisymmetry of signed order up to signed equivalence -----------------
(def signed-at-most-antisymmetric-spec
  {:name 'signed/at-most-antisymmetric :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['ab (sle 'a 'b)] ['ba (sle 'b 'a)]]
          (seq-equiv 'a 'b))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['ab (sle 'a 'b)] ['ba (sle 'b 'a)]]
    (let [A (radd (pos 'a) (neg 'b))
          B (radd (pos 'b) (neg 'a))
          left-cross (nmul (num A) (den B))
          right-cross (nmul (num B) (den A))
          ab-cross (rat-to-cross A B 'ab)
          ba-cross (rat-to-cross B A 'ba)]
      (nat-antisymmetric left-cross right-cross ab-cross ba-cross)))})

;; ---- signed Archimedean reciprocal-band lemma ------------------------------
(def reciprocal-close-equivalent-spec
  {:name 'analysis/equivalent-of-reciprocal-close :universes []
   :type
   (function/forall
    [['x signed] ['y signed]
     ['bounded
      (function/forall
       [['k nat]]
       (close 'x (from-nnrat (make one-nat 'k)) 'y))]]
    (seq-equiv 'x 'y))
   :value
   (function/lam
    [['x signed] ['y signed]
     ['bounded
      (function/forall
       [['k nat]]
       (close 'x (from-nnrat (make one-nat 'k)) 'y))]]
    (let [Px (pos 'x) Nx (neg 'x) Py (pos 'y) Ny (neg 'y)
          A (radd Px Ny)
          B (radd Py Nx)
          ;; x-r <= y gives A <= B+r for every reciprocal r.
          A-bounded
          (function/lam
           [['k nat]]
           (let [r (make one-nat 'k)
                 eps (from-nnrat r)
                 x-low (ssub 'x eps)
                 raw-left (radd (radd Px nnrat-zero) Ny)
                 raw-right (radd Py (radd Nx r))
                 A-plus (radd B r)
                 band (app 'bounded 'k)
                 lower (prop-left (sle x-low 'y) (sle 'y (sadd 'x eps)) band)
                 raw-left-to-A
                 (rat-add-respects (radd Px nnrat-zero) Px Ny Ny
                                   (rat-add-zero-right Px) (rat-refl Ny))
                 A-to-raw-left (rat-sym raw-left A raw-left-to-A)
                 A-plus-to-raw-right (rat-add-assoc Py Nx r)]
             (rat-at-most-respects A raw-left A-plus raw-right
                                  A-to-raw-left A-plus-to-raw-right lower)))
          ;; y <= x+r gives B <= A+r for every reciprocal r.
          B-bounded
          (function/lam
           [['k nat]]
           (let [r (make one-nat 'k)
                 eps (from-nnrat r)
                 x-high (sadd 'x eps)
                 raw-left (radd Py (radd Nx nnrat-zero))
                 raw-right (radd (radd Px r) Ny)
                 B-plus (radd A r)
                 band (app 'bounded 'k)
                 upper (prop-right (sle (ssub 'x eps) 'y) (sle 'y x-high) band)
                 raw-left-to-B
                 (rat-add-respects Py Py (radd Nx nnrat-zero) Nx
                                   (rat-refl Py) (rat-add-zero-right Nx))
                 B-to-raw-left (rat-sym raw-left B raw-left-to-B)
                 raw-right-to-B-plus (rat-reorder-three Px r Ny)
                 B-plus-to-raw-right
                 (rat-sym raw-right B-plus raw-right-to-B-plus)]
             (rat-at-most-respects B raw-left B-plus raw-right
                                  B-to-raw-left B-plus-to-raw-right upper)))
          xy (rat-arch A B A-bounded)
          yx (rat-arch B A B-bounded)]
      (signed-antisym 'x 'y xy yx)))})

;; ---- uniqueness of signed-rational limits ----------------------------------
(def limit-unique-spec
  {:name 'analysis/limit-unique :universes []
   :type
   (function/forall
    [['s sig-seq] ['L signed] ['L-prime signed]
     ['M modulus] ['M-prime modulus]
     ['to-L (converges 's 'L 'M)]
     ['to-L-prime (converges 's 'L-prime 'M-prime)]]
    (seq-equiv 'L 'L-prime))
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['L-prime signed]
     ['M modulus] ['M-prime modulus]
     ['to-L (converges 's 'L 'M)]
     ['to-L-prime (converges 's 'L-prime 'M-prime)]]
    (let [reciprocal-bands
          (function/lam
           [['k nat]]
           (let [r (make one-nat 'k)
                 eps (from-nnrat r)
                 ma (app 'M eps)
                 mb (app 'M-prime signed-zero)
                 n (nadd ma mb)
                 ma<=n
                 (witness-nat
                  (function/lam [['extra nat]] (eq-nat (nadd ma 'extra) n))
                  mb (reflexive-nat n))
                 mb<=n
                 (witness-nat
                  (function/lam [['extra nat]] (eq-nat (nadd mb 'extra) n))
                  ma (app (function/const* 'nat/add-commutative []) mb ma))
                 sn (app 's n)
                 L-low (ssub 'L eps)
                 L-high (sadd 'L eps)
                 Lp-low (ssub 'L-prime signed-zero)
                 Lp-high (sadd 'L-prime signed-zero)
                 around-L (app 'to-L eps n ma<=n)
                 around-Lp-zero (app 'to-L-prime signed-zero n mb<=n)
                 L-low<=sn
                 (prop-left (sle L-low sn) (sle sn L-high) around-L)
                 sn<=L-high
                 (prop-right (sle L-low sn) (sle sn L-high) around-L)
                 Lp-low<=sn
                 (prop-left (sle Lp-low sn) (sle sn Lp-high) around-Lp-zero)
                 sn<=Lp-high
                 (prop-right (sle Lp-low sn) (sle sn Lp-high) around-Lp-zero)
                 Lp-zero-eq-Lp
                 (app (function/const* 'signed/add-zero-right []) 'L-prime)
                 Lp<=sn
                 (signed-at-most-respects
                  Lp-low 'L-prime sn sn Lp-zero-eq-Lp (signed-refl sn) Lp-low<=sn)
                 sn<=Lp
                 (signed-at-most-respects
                  sn sn Lp-high 'L-prime (signed-refl sn) Lp-zero-eq-Lp sn<=Lp-high)
                 L-low<=Lp (signed-trans L-low sn 'L-prime L-low<=sn sn<=Lp)
                 Lp<=L-high (signed-trans 'L-prime sn L-high Lp<=sn sn<=L-high)]
             (conjoin (sle L-low 'L-prime) (sle 'L-prime L-high)
                      L-low<=Lp Lp<=L-high)))]
      (app (function/const* 'analysis/equivalent-of-reciprocal-close [])
           'L 'L-prime reciprocal-bands)))})

(def definition-specs [])
(def theorem-specs
  [signed-add-zero-right-spec
   signed-at-most-antisymmetric-spec
   reciprocal-close-equivalent-spec
   limit-unique-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      arch/extend-environment
      respects/extend-environment
      identities/extend-environment
      (support/extend-with :signed-limit-uniqueness theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
