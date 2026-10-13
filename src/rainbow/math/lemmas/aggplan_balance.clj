(ns rainbow.math.lemmas.aggplan-balance
  "General lemmas: aggplan balance. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn flow-step [x i o t] (eqv (add (at x (s/succ t)) (at o t)) (add (at x t) (at i t))))

(def flow-telescope-spec
  (let [x 'ft-x i 'ft-i o 'ft-o
        claim (fn [m] (f/forall [['ft-h (s/all-below m #(flow-step x i o %))]]
                                (eqv (add (at x m) (sum o m)) (add (at x s/nz) (sum i m)))))]
    (s/spec 'signed/flow-telescope [['ft-x family] ['ft-i family] ['ft-o family] ['ft-m nat]]
            (claim 'ft-m)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['ft-k nat]] (claim 'ft-k))
                   ;; sum F 0 unfolds to 0
                   (f/lam [['ft-h (s/all-below s/nz #(flow-step x i o %))]] (refl (add (at x s/nz) s/zero)))
                   (f/lam [['ft-j nat] ['ft-ih (claim 'ft-j)] ['ft-h (s/all-below (s/succ 'ft-j) #(flow-step x i o %))]]
                          (let [j 'ft-j xj (at x j) xj1 (at x (s/succ j)) x0 (at x s/nz) oj (at o j) ij (at i j)
                                So (sum o j) Si (sum i j)
                                weak (f/lam [['ft-t nat] ['ft-tl (below 'ft-t j)]] (at 'ft-h 'ft-t (call 'nat/strict-below-weaken 'ft-t j 'ft-tl)))
                                prev (at 'ft-ih weak)
                                step (at 'ft-h j (s/self-below j))]
                            ;; sum F (j + 1) unfolds to sum F j + F j
                            (a/chain (add xj1 (add So oj))
                                     [(add (add xj1 oj) So) (ring (add xj1 (add So oj)) (add (add xj1 oj) So))]
                                     [(add (add xj ij) So) (s/add-cong (add xj1 oj) (add xj ij) So So step (refl So))]
                                     [(add (add xj So) ij) (ring (add (add xj ij) So) (add (add xj So) ij))]
                                     [(add (add x0 Si) ij) (s/add-cong (add xj So) (add x0 Si) ij ij prev (refl ij))]
                                     [(add x0 (add Si ij)) (ring (add (add x0 Si) ij) (add x0 (add Si ij)))])))
                   'ft-m))))

(defn kW [k W] (f/lam [['ak-i nat]] (mul k (at W 'ak-i))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(defn balance [G x i o lo hi tag]
  (let [t (symbol (str tag "-t")) h (symbol (str tag "-h"))]
    (at (call 'signed/flow-telescope x i o 'n)
        (f/lam [[t nat] [h (below t 'n)]]
               (anti (add (at x (s/succ t)) (at o t)) (add (at x t) (at i t)) (at (G lo) t h) (at (G hi) t h))))))

(def theorem-specs [flow-telescope-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nat-more/extend-environment
      add-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-aggplan-balance theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
