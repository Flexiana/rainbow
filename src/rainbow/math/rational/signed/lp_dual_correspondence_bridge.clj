(ns rainbow.math.rational.signed.lp-dual-correspondence-bridge
  "Collect original inequality/free-equality prices into actual expanded dual
  columns and objective. Proof producer only; actual data remains in every target."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-feasibility-bridge :as feasibility]
            [rainbow.math.rational.signed.lp-equality-row-bridge :as row]
            [rainbow.math.rational.signed.lp-equality-price-bridge :as price]
            [rainbow.math.rational.signed.pointwise-order :as pointwise]
            [rainbow.math.rational.signed.add-associative :as associative]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def zero (f/const* 'signed/zero []))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- add [a b] (app 'signed/add a b))
(defn- mul [a b] (app 'signed/multiply a b))
(defn- neg [a] (app 'signed/negate a))
(defn- sym [a b h] (app 'signed/equivalent-symmetric a b h))
(defn- trans [a b c h k] (app 'signed/equivalent-transitive a b c h k))
(defn- literal [x] (#'lp/signed-literal x))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv literal xs))
      (f/lam [['index lp/nat]] zero)))
(defn- matrix [rows]
  (if (seq rows) (#'lp/nat-lookup (f/arrow lp/nat lp/signed) (mapv mapping rows))
      (f/lam [['row-index lp/nat]] (mapping []))))
(defn- sum [m indices] (poly 'signed/map-sum lp/nat m indices))
(defn- weighted [m y indices]
  (sum (f/lam [['i lp/nat]] (mul (f/app m 'i) (f/app y 'i))) indices))
(defn- conjunction-proof [specs]
  (reduce (fn [tail spec]
            {:type (app 'proposition/conjunction (:type spec) (:type tail))
             :value (app 'proposition/conjoin (:type spec) (:type tail) (:value spec) (:value tail))})
          {:type (f/const* 'proposition/truth []) :value (f/const* 'proposition/trivial [])}
          (reverse specs)))

(defn- collect-contributions [blocks]
  (if (empty? blocks)
    {:original zero :actual zero :proof (app 'signed/equivalent-reflexive zero)}
    (let [{O :original entries :actual h :proof} (first blocks)
          tail (collect-contributions (rest blocks))
          OT (:original tail) AT (:actual tail) [A B] entries
          pair? (= 2 (count entries)) head (if pair? (add A B) A)
          original (add O OT) middle (add head AT)
          actual (if pair? (add A (add B AT)) middle)
          combined (app 'signed/add-respects-equivalence O head OT AT h (:proof tail))]
      {:original original :actual actual
       :proof (if pair? (trans original middle actual combined (app 'signed/add-associative A B AT)) combined)})))

(defn dual-correspondence-specs
  "Four obligations: original/actual price relations, actual price nonnegativity,
  EVERY Nat dual column, and full dual objective. Sum proofs use row/price
  correspondences and additive collection, not host-computed aggregate values.
  Original dual sums list inequality rows then unsplit equality rows. No objective
  sense flip, dual feasibility, submitted-plan or optimality claim is made here."
  [original actual]
  ;; Shared internal shape/scalar guard; no prior proof is trusted by invoking it.
  (#'feasibility/validate! original actual)
  (let [eqs (get original :equalities []) free (get original :equality-prices [])
        base (count (:matrix original))
        bounded? (fn [x] (and (or (integer? x) (ratio? x))
                              (<= -10000 (if (ratio? x) (numerator x) x) 10000)
                              (<= 1 (if (ratio? x) (denominator x) 1) 10000)))]
    (when-not (and (vector? (:prices original)) (vector? (:prices actual)) (vector? free)
                   (= base (count (:prices original))) (= (count eqs) (count free))
                   (= (count (:matrix actual)) (count (:prices actual))))
      (throw (ex-info "Original and actual prices must match their row counts"
                      {:error/category :lp-dual-correspondence/price-shape})))
    (when-not (every? bounded? (concat (:prices original) (:prices actual) free))
      (throw (ex-info "Expected bounded exact prices before encoding"
                      {:error/category :lp-dual-correspondence/invalid-price})))
    (let [price-bundles (price/equality-price-specs free (:prices actual) base)
          prefix
          (mapv (fn [i]
                  (let [o (nth (:matrix original) i) a (nth (:matrix actual) i)
                        b (nth (:capacities original) i) ab (nth (:capacities actual) i)
                        proofs (row/inequality-row-specs o b a ab)
                        p (literal (nth (:prices original) i)) ap (literal (nth (:prices actual) i))]
                    {:o (mapping o) :a (mapping a) :b (literal b) :ab (literal ab)
                     :coeff (:value (:coefficients proofs)) :rhs (:value (:rhs proofs))
                     :p p :ap ap :price {:type (eqv ap p) :value (#'lp/computed-equivalence ap p)}})) (range base))
          pairs
          (mapv (fn [i]
                  (let [{o :row b :value} (nth eqs i) j (+ base (* 2 i))
                        a (nth (:matrix actual) j) n (nth (:matrix actual) (inc j))
                        ab (nth (:capacities actual) j) nb (nth (:capacities actual) (inc j))
                        proofs (row/row-pair-specs o b a ab n nb)]
                    {:o (mapping o) :a (mapping a) :n (mapping n)
                     :b (literal b) :ab (literal ab) :nb (literal nb)
                     :positive (:value (:positive-coefficients proofs)) :negative (:value (:negative-coefficients proofs))
                     :positive-rhs (:value (:positive-rhs proofs)) :negative-rhs (:value (:negative-rhs proofs))
                     :p (literal (nth free i)) :pp (literal (nth (:prices actual) j))
                     :pm (literal (nth (:prices actual) (inc j)))
                     :price-specs (:specs (nth price-bundles i))})) (range (count eqs)))
          blocks
          (fn [rhs?]
            (into
             (mapv (fn [{:keys [o a b ab coeff rhs p ap price]}]
                     (let [v (if rhs? b (f/app o 'column)) av (if rhs? ab (f/app a 'column))
                           same (if rhs? rhs (f/app coeff 'column))]
                       {:original (mul v p) :actual [(mul av ap)]
                        :proof (app 'signed/multiply-respects-equivalence v av p ap
                                    (sym av v same) (sym ap p (:value price)))})) prefix)
             (mapv (fn [{:keys [o a n b ab nb positive negative positive-rhs negative-rhs p pp pm price-specs]}]
                     (let [v (if rhs? b (f/app o 'column)) av (if rhs? ab (f/app a 'column))
                           nv (if rhs? nb (f/app n 'column))
                           ps (if rhs? positive-rhs (f/app positive 'column))
                           ns (if rhs? negative-rhs (f/app negative 'column))
                           O (mul v p) ideal (add (mul v pp) (mul (neg v) pm))
                           A (mul av pp) B (mul nv pm)]
                       {:original O :actual [A B]
                        :proof (trans O ideal (add A B)
                                      (f/app (:value (:universal-contribution price-specs)) v)
                                      (app 'signed/add-respects-equivalence (mul v pp) A (mul (neg v) pm) B
                                           (app 'signed/multiply-right-respects-equivalence v av pp (sym av v ps))
                                           (app 'signed/multiply-right-respects-equivalence (neg v) nv pm (sym nv (neg v) ns))))})) pairs)))
          original-rows (into (:matrix original) (map :row eqs))
          original-rhs (into (:capacities original) (map :value eqs))
          original-prices (into (:prices original) free)
          OM (matrix original-rows) AM (matrix (:matrix actual))
          OY (mapping original-prices) AY (mapping (:prices actual))
          OI (#'lp/index-list (count original-rows)) AI (#'lp/index-list (count (:matrix actual)))
          column-sum (fn [M y indices]
                       (weighted (f/lam [['i lp/nat]] (f/app (f/app M 'i) 'column)) y indices))
          original-column (column-sum OM OY OI) actual-column (column-sum AM AY AI)
          original-objective (weighted (mapping original-rhs) OY OI)
          actual-objective (weighted (mapping (:capacities actual)) AY AI)
          zero-on (f/lam [['ignored lp/nat]] zero)]
      (array-map
       :price-correspondence (conjunction-proof (concat (map :price prefix) (map #(get-in % [:price-specs :split]) pairs)))
       :actual-prices-nonnegative
       {:type (poly 'signed/all-at-most lp/nat zero-on AY AI)
        :value (#'lp/all-at-most-proof zero-on AY (count (:prices actual)))}
       :dual-columns {:type (f/forall [['column lp/nat]] (eqv original-column actual-column))
                      :value (f/lam [['column lp/nat]] (:proof (collect-contributions (blocks false))))}
       :dual-objective {:type (eqv original-objective actual-objective)
                        :value (:proof (collect-contributions (blocks true)))}))))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-equality-row-bridge rainbow.math.rational.signed.lp-equality-price-bridge rainbow.math.rational.signed.pointwise-order rainbow.math.rational.signed.add-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-dual-correspondence-bridge))
