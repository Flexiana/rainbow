(ns rainbow.math.sums.bpath-walk
  "Finite one-hot walks crossing a binary cut. Signed weights are unrestricted;
  the bottleneck aggregate is seeded by the first edge, never by zero."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum le eqv below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.one-hot-factor :as factor]
            [rainbow.math.sums.bpath-cut :as cut]
            [rainbow.math.rational.signed.indexed-max-dominates :as imax]))
(def bit-upper-spec
  (s/spec 'signed/binary-at-least-one-is-one
    [['bw-x signed] ['bw-bit (cut/bit 'bw-x)] ['bw-lower (le a/one 'bw-x)]]
    (eqv 'bw-x a/one)
    (a/cases (eqv 'bw-x s/zero) (eqv 'bw-x a/one) (eqv 'bw-x a/one)
      (cut/bit-to-cases 'bw-x 'bw-bit)
      (f/lam [['bw-zero (eqv 'bw-x s/zero)]]
        (call 'proposition/explode (eqv 'bw-x a/one)
          (call 'signed/one-not-at-most-zero
            (s/le-transport a/one a/one 'bw-x s/zero (s/refl a/one) 'bw-zero 'bw-lower))))
      (f/lam [['bw-one (eqv 'bw-x a/one)]] 'bw-one))))
(def bit-lower-spec
  (s/spec 'signed/binary-at-most-zero-is-zero
    [['bw-x signed] ['bw-bit (cut/bit 'bw-x)] ['bw-upper (le 'bw-x s/zero)]]
    (eqv 'bw-x s/zero)
    (a/cases (eqv 'bw-x s/zero) (eqv 'bw-x a/one) (eqv 'bw-x s/zero)
      (cut/bit-to-cases 'bw-x 'bw-bit)
      (f/lam [['bw-zero (eqv 'bw-x s/zero)]] 'bw-zero)
      (f/lam [['bw-one (eqv 'bw-x a/one)]]
        (call 'proposition/explode (eqv 'bw-x s/zero)
          (call 'signed/one-not-at-most-zero
            (s/le-transport 'bw-x a/one s/zero s/zero 'bw-one (s/refl s/zero) 'bw-upper)))))))
(defn steps [Q W n]
  (f/lam [['bw-position nat]]
    (cut/weight (cut/row Q 'bw-position) (cut/row Q (s/succ 'bw-position)) W n)))
(defn rows-binary [Q n M]
  (f/forall [['bw-binary-row nat] ['bw-binary-row-bound (below 'bw-binary-row (s/succ M))]]
    (factor/binary (cut/row Q 'bw-binary-row) n)))
(defn rows-unit [Q n M]
  (s/all-below (s/succ M) #(eqv (sum (cut/row Q %) n) a/one)))
(defn edge-steps [Q E n M]
  (s/all-below M #(eqv (at (steps Q E n) %) a/one)))
(defn bound-witness [F n b]
  (f/lam [['bw-hit nat]] (cut/both (below 'bw-hit n) (le b (at F 'bw-hit)))))
(defn walk-params [Q E S W n M b]
  [[Q cut/matrix] [E cut/matrix] [S family] [W cut/matrix] [n nat] [M nat] [b signed]
   ['bw-rows-binary (rows-binary Q n M)] ['bw-rows-unit (rows-unit Q n M)]
   ['bw-edges (edge-steps Q E n M)] ['bw-cut-binary (factor/binary S n)]
   ['bw-source (le a/one (cut/side (cut/row Q s/nz) S n))]
   ['bw-sink (le (cut/side (cut/row Q M) S n) s/zero)]
   ['bw-cuts (cut/all2 n #(le (cut/crossing E S b W %1 %2) s/zero))]])
(def walk-witness-spec
  (let [Q 'bw-Q E 'bw-E S 'bw-S W 'bw-W n 'bw-n M 'bw-M b 'bw-b
        Z (f/lam [['bw-zpos nat]] (cut/side (cut/row Q 'bw-zpos) S n))
        F (steps Q W n) goal (cut/exists (bound-witness F M b))
        bit-at (fn [i hi]
                 (call 'signed/one-hot-selects-binary-value (cut/row Q i) S n
                   (at 'bw-rows-binary i hi) (at 'bw-rows-unit i hi) 'bw-cut-binary))
        zero-below (f/app (f/const* 'proposition/witness [cut/tl]) nat
                     (f/lam [['bw-extra nat]] (a/enat (a/nadd (s/succ s/nz) 'bw-extra) (s/succ M)))
                     M (a/nr (s/succ M)))
        allbits (f/lam [['bw-zidx nat] ['bw-zh (below 'bw-zidx (s/succ M))]] (bit-at 'bw-zidx 'bw-zh))
        start (call 'signed/binary-at-least-one-is-one (at Z s/nz) (bit-at s/nz zero-below) 'bw-source)
        end (call 'signed/binary-at-most-zero-is-zero (at Z M) (bit-at M (s/self-below M)) 'bw-sink)]
    (s/spec 'signed/one-hot-walk-cut-bound-witness (walk-params Q E S W n M b) goal
      (at (call 'signed/binary-sequence-exit Z M allbits start end) goal
        (f/lam [['bw-exit nat] ['bw-exit-proof (at (cut/exit-predicate Z M) 'bw-exit)]]
          (let [t 'bw-exit tt (s/succ t)
                endpoints (cut/both (eqv (at Z t) a/one) (eqv (at Z tt) s/zero))
                ht (cut/left (below t M) endpoints 'bw-exit-proof)
                inside-outside (cut/right (below t M) endpoints 'bw-exit-proof)
                hrow (s/weaken t M ht)
                hnext (call 'nat/successor-monotone (s/succ t) M ht)
                bound (call 'signed/one-hot-cut-exit-weight-bound
                        (cut/row Q t) (cut/row Q tt) E S W n b
                        (at 'bw-rows-binary t hrow) (at 'bw-rows-unit t hrow)
                        (at 'bw-rows-binary tt hnext) (at 'bw-rows-unit tt hnext)
                        (at 'bw-edges t ht)
                        (cut/left (eqv (at Z t) a/one) (eqv (at Z tt) s/zero) inside-outside)
                        (cut/right (eqv (at Z t) a/one) (eqv (at Z tt) s/zero) inside-outside)
                        'bw-cuts)]
            (cut/witness (bound-witness F M b) t
              (cut/pair (below t M) (le b (at F t)) ht bound))))))))
(defn maximum [F n] (call 'signed/indexed-max-from F (at F s/nz) n))
(def max-upper-spec
  (let [F 'bw-F init 'bw-init R 'bw-R n 'bw-n
        upper (fn [k] (s/all-below k #(le (at F %) R)))
        agg (fn [k] (call 'signed/indexed-max-from F init k))
        claim (fn [k] (f/arrow (upper k) (le (agg k) R)))]
    (s/spec 'signed/indexed-max-from-upper-bound
      [[F family] [init signed] [R signed] [n nat] ['bw-init-upper (le init R)]]
      (claim n)
      (f/app (f/const* 'data/Nat.rec [cut/pl])
        (f/lam [['bw-length nat]] (claim 'bw-length))
        (f/lam [['bw-empty (upper s/nz)]] 'bw-init-upper)
        (f/lam [['bw-k nat] ['bw-ih (claim 'bw-k)] ['bw-all (upper (s/succ 'bw-k))]]
          (call 'signed/at-most-max (agg 'bw-k) (at F 'bw-k) R
            (at 'bw-ih (f/lam [['bw-j nat] ['bw-jh (below 'bw-j 'bw-k)]]
                         (at 'bw-all 'bw-j (s/weaken 'bw-j 'bw-k 'bw-jh))))
            (at 'bw-all 'bw-k (s/self-below 'bw-k)))) n))))
(def witness-max-spec
  (let [F 'bw-F n 'bw-n b 'bw-b goal (le b (maximum F n))]
    (s/spec 'signed/indexed-max-lower-of-bound-witness
      [[F family] [n nat] [b signed] ['bw-witness (cut/exists (bound-witness F n b))]] goal
      (at 'bw-witness goal
        (f/lam [['bw-i nat] ['bw-hit-proof (at (bound-witness F n b) 'bw-i)]]
          (call 'signed/at-most-transitive b (at F 'bw-i) (maximum F n)
            (cut/right (below 'bw-i n) (le b (at F 'bw-i)) 'bw-hit-proof)
            (call 'signed/indexed-max-from-dominates F (at F s/nz) n 'bw-i
              (cut/left (below 'bw-i n) (le b (at F 'bw-i)) 'bw-hit-proof))))))))
(def witness-attains-spec
  (let [F 'bw-F n 'bw-n b 'bw-b goal (eqv (maximum F n) b)]
    (s/spec 'signed/indexed-max-attains-bound-of-witness
      [[F family] [n nat] [b signed]
       ['bw-upper (s/all-below n #(le (at F %) b))]
       ['bw-witness (cut/exists (bound-witness F n b))]] goal
      (at 'bw-witness goal
        (f/lam [['bw-i nat] ['bw-hit-proof (at (bound-witness F n b) 'bw-i)]]
          (let [hi (cut/left (below 'bw-i n) (le b (at F 'bw-i)) 'bw-hit-proof)
                zero-succ (f/app (f/const* 'proposition/witness [cut/tl]) nat
                            (f/lam [['bw-extra nat]] (a/enat (a/nadd (s/succ s/nz) 'bw-extra) (s/succ 'bw-i)))
                            'bw-i (a/nr (s/succ 'bw-i)))
                hn (call 'nat/at-most-transitive (s/succ s/nz) (s/succ 'bw-i) n zero-succ hi)]
            (call 'signed/at-most-antisymmetric (maximum F n) b
              (call 'signed/indexed-max-from-upper-bound F (at F s/nz) b n
                (at 'bw-upper s/nz hn) 'bw-upper)
              (call 'signed/indexed-max-lower-of-bound-witness F n b 'bw-witness))))))))
(def walk-lower-spec
  (let [Q 'bw-Q E 'bw-E S 'bw-S W 'bw-W n 'bw-n M 'bw-M b 'bw-b]
    (s/spec 'signed/one-hot-walk-bottleneck-lower-bound (walk-params Q E S W n M b)
      (le b (maximum (steps Q W n) M))
      (call 'signed/indexed-max-lower-of-bound-witness (steps Q W n) M b
        (call 'signed/one-hot-walk-cut-bound-witness Q E S W n M b
          'bw-rows-binary 'bw-rows-unit 'bw-edges 'bw-cut-binary 'bw-source 'bw-sink 'bw-cuts)))))
(def walk-attains-spec
  (let [Q 'bw-Q E 'bw-E S 'bw-S W 'bw-W n 'bw-n M 'bw-M b 'bw-b]
    (s/spec 'signed/one-hot-walk-bottleneck-attains
      (conj (walk-params Q E S W n M b) ['bw-upper (s/all-below M #(le (at (steps Q W n) %) b))])
      (eqv (maximum (steps Q W n) M) b)
      (call 'signed/indexed-max-attains-bound-of-witness (steps Q W n) M b 'bw-upper
        (call 'signed/one-hot-walk-cut-bound-witness Q E S W n M b
          'bw-rows-binary 'bw-rows-unit 'bw-edges 'bw-cut-binary 'bw-source 'bw-sink 'bw-cuts)))))
(def theorem-specs [bit-upper-spec bit-lower-spec walk-witness-spec max-upper-spec
                    witness-max-spec witness-attains-spec walk-lower-spec walk-attains-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.bpath-cut rainbow.math.rational.signed.indexed-max-dominates])

(defn install
  "Adds this module's own declarations."
  [env]
  (reduce (fn [e spec] (println :bpath-walk :installing (:name spec)) (flush) (support/add-spec-shared e :expr-sum-bpath-walk spec)) env theorem-specs))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.bpath-walk))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
