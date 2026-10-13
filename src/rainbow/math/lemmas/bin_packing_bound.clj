(ns rainbow.math.lemmas.bin-packing-bound
  "General lemmas: bin packing bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.order-monotone :as monotone]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.rational.signed.strict-order :as strict]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn eta [w] (f/lam [['wi nat]] (at w 'wi)))

(defn capacity-sum "K' C as the checker writes it: K' copies of C" [C Kp] (sum (f/lam [['ck nat]] C) Kp))

(defn load [X w n k] (sum (f/lam [['li nat]] (mul (at X k 'li) (at w 'li))) n))

(defn columns-one [X Kp n] (s/all-below n #(eqv (sum (f/lam [['ck nat]] (at X 'ck %)) Kp) one)))

(defn loads-at-most [X w C Kp n] (s/all-below Kp #(le (load X w n %) C)))

(def volume-bound-spec
  (let [Kp 'Kp n 'n
        L (f/lam [['lk nat] ['li nat]] (mul (at 'X 'lk 'li) (at 'w 'li)))
        loads (f/lam [['lk nat]] (load 'X 'w n 'lk))
        total (sum (eta 'w) n) cap (capacity-sum 'C Kp)
        per-item (f/lam [['pi nat]] (sum (f/lam [['pk nat]] (at L 'pk 'pi)) Kp))
        load-total (a/chain (sum loads Kp)
                            [(sum per-item n) (call 'signed/expr-sum-value-swap L n Kp)]
                            [total (a/sum-cong per-item (eta 'w) n 'ti
                                               (fn [i hi]
                                                 (let [col (f/lam [['ck nat]] (at 'X 'ck i)) wi (at 'w i)]
                                                   (a/chain (at per-item i)
                                                            [(mul (sum col Kp) wi)
                                                             (sym (mul (sum col Kp) wi) (at per-item i)
                                                                  (call 'signed/expr-sum-value-scale-right col wi Kp))]
                                                            [(mul one wi) (a/mul-cong (sum col Kp) one wi wi (at 'hcols i hi) (refl wi))]
                                                            [wi (call 'signed/multiply-one-left wi)]))))])
        total-le-cap (le-resp (sum loads Kp) total cap cap load-total (refl cap)
                              (call 'signed/expr-sum-value-monotone-below loads (f/lam [['ck nat]] 'C) Kp 'hloads))
        cap-g-le-cap (le-trans (add cap 'g) total cap 'hbound total-le-cap)
        g-np (le-resp (add (add cap 'g) (neg cap)) 'g (add cap (neg cap)) s/zero
                      (ring (add (add cap 'g) (neg cap)) 'g) (ring (add cap (neg cap)) s/zero)
                      (call 'signed/add-right-monotone (add cap 'g) cap (neg cap) cap-g-le-cap))
        g-nn (call 'signed/less-than-implies-at-most s/zero 'g 'hg)]
    (s/spec 'signed/bin-packing-volume-bound
            [['w family] ['C signed] ['g signed] ['X matrix] ['Kp nat] ['n nat]
             ['hg (call 'signed/less-than s/zero 'g)]
             ['hbound (le (add cap 'g) total)]
             ['hcols (columns-one 'X Kp n)] ['hloads (loads-at-most 'X 'w 'C Kp n)]]
            falsity
            (at (call 'proposition/right (le s/zero 'g) (call 'proposition/negation (eqv s/zero 'g)) 'hg)
                (call 'signed/at-most-antisymmetric s/zero 'g g-nn g-np)))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [volume-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env s/extend-environment a/extend-environment monotone/extend-environment units/extend-environment strict/extend-environment (support/extend-with :expr-sum-bin-packing-bound theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.bin-packing-bound))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
