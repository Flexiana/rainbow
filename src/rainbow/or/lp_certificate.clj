(ns rainbow.or.lp-certificate
  "Turn numeric LP data into a kernel-checked optimality certificate.

  This is the per-instance end of the verified-optimization pipeline. The
  expensive theorem -- `optimization/signed-lp-optimality-certificate-on`, proved
  once for every matrix, cost vector, dual vector, row list and column list -- is
  reused unchanged. What happens per instance is only arithmetic:

    * every coefficient is encoded as an exact signed rational, so negative costs
      and negative coefficients are ordinary data rather than a special case;
    * every feasibility, dual-feasibility and nonnegativity condition is decided
      by `signed/decide-at-most`, and reflexivity records that the decision
      returned true;
    * the resulting facts are folded into the list-quantified hypotheses the
      theorem wants and the kernel checks the instantiation.

  `certify` returns `:certified` only when the kernel accepts. A wrong plan, an
  infeasible plan, a dual vector that does not close the gap, or arithmetic that
  does not reduce all produce `:rejected` with the kernel's own reason -- a
  checker that accepted bad certificates would be worse than no checker.

  Nothing here is trusted. This namespace only BUILDS proof data; the guarantee
  comes from `rainbow.kernel` checking it, and `certify` reports the axiom
  closure so a reader can see the proof rests on nothing."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-certificate-reflect :as reflect]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.module :as module]))

(def schema-version 1)

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [f xs]
  (app (function/const* 'signed/map-sum [zero-level]) nat f xs))
(defn- all-at-most [f g xs]
  (app (function/const* 'signed/all-at-most [zero-level]) nat f g xs))

;; ---- encoding numbers -------------------------------------------------------

(defn- numeral [n]
  ;; Surface literals elaborate to compact kernel naturals. Keep coefficients,
  ;; denominator predecessors and index lists independent of numeral magnitude.
  [:nat n])

(defn- nnrat-literal
  "n/d as an nnrat, with d strictly positive. `nnrat/make` takes the denominator
  PREDECESSOR, so a whole number k is `make k 0`."
  [n d]
  (app (function/const* 'nnrat/make []) (numeral n) (numeral (dec d))))

(defn- rational-parts
  "Numerator and denominator of any Clojure rational. `numerator` is defined only
  on Ratio, so whole numbers are handled directly."
  [value]
  (let [exact (rationalize value)]
    (if (ratio? exact)
      [(numerator exact) (denominator exact)]
      [(long exact) 1])))

(defn- signed-literal
  "An exact signed rational from any Clojure rational, negative included. A
  signed value is a Grothendieck pair, so -3 is the pair (0, 3)."
  [value]
  (let [[n d] (rational-parts value)]
    (app (function/const* 'signed/make [])
         (nnrat-literal (max n 0) d)
         (nnrat-literal (max (- n) 0) d))))

;; ---- encoding vectors as functions on nat indices ---------------------------

(def ^:dynamic *table-encoding*
  "How instance vectors and matrices are written as `nat -> X` functions: :linear (the
  default; nested Nat.rec, O(i) steps to reach entry i) or :binary (a balanced tree of
  index comparisons, O(log n) steps). The encoding is part of the claim's statement, so
  :linear stays the default and existing certificates keep their ids."
  :linear)

(defn- binary-lookup
  "A `nat -> X` function reading a fixed vector by a balanced tree of comparisons of
  the index with absolute midpoints: entry k at index k, the last entry past the end."
  [carrier values]
  (let [motive (function/lam [['ignored bool]] carrier)]
    (letfn [(build [lo values]
              (if (= 1 (count values))
                (first values)
                (let [half (quot (count values) 2)
                      mid (+ lo half)]
                  ;; Bool.rec takes the false case first: index < mid goes left
                  (app (function/const* 'data/Bool.rec [type-level])
                       motive
                       (build lo (subvec values 0 half))
                       (build mid (subvec values half))
                       (app (function/const* 'nat/decide-at-most []) [:nat mid] 'lookup-index)))))]
      (function/lam [['lookup-index nat]] (build 0 (vec values))))))

(defn- nat-lookup
  "A `nat -> X` function reading a fixed vector, as nested `Nat.rec`. Index 0
  gives the first entry and any index past the end gives the last, which is
  harmless because the theorems only ever evaluate at listed indices."
  [carrier values]
  (let [values (vec values)
        motive (function/lam [['ignored nat]] carrier)]
    (when (empty? values)
      (throw (ex-info "An LP needs at least one row and one column"
                      {:error/category :lp-certificate/empty-instance})))
    (if (= :binary *table-encoding*)
      (binary-lookup carrier values)
    ;; each level peels one successor, so the tail must scrutinize the
    ;; PREDECESSOR the step bound, not the original index
    (letfn [(build [remaining scrutinee]
              (if (= 1 (count remaining))
                (first remaining)
                (app (function/const* 'data/Nat.rec [type-level])
                     motive
                     (first remaining)
                     (function/lam [['predecessor nat] ['ignored carrier]]
                                   (build (subvec remaining 1) 'predecessor))
                     scrutinee)))]
      (function/lam [['lookup-index nat]] (build values 'lookup-index))))))

(defn- index-range
  "The list of index numerals `from` (inclusive) to `to` (exclusive)."
  [from to]
  (reduce (fn [tail index]
            (app (function/const* 'data/cons [type-level]) nat
                 (numeral index) tail))
          (app (function/const* 'data/nil [type-level]) nat)
          (reverse (range from to))))

(defn- index-list [count-of] (index-range 0 count-of))

;; ---- discharging conditions by computation ----------------------------------

(defn- decided-at-most [a b]
  (app (function/const* 'signed/decide-at-most-true-sound []) a b
       (app (function/const* 'equality/reflexive [type-level]) bool bool-true)))

(defn- all-at-most-proof
  "Folds one decided comparison per index into the list-quantified hypothesis.

  `signed/all-at-most` recurses on the TAIL, so the proof for index i is built
  against the suffix after i, not against the prefix before it."
  [f g index-count]
  (reduce
   (fn [rest-proof index]
     (let [head (numeral index)
           tail (index-range (inc index) index-count)]
       (app (function/const* 'signed/all-at-most-cons [zero-level])
            nat f g head tail
            (decided-at-most (app f head) (app g head))
            rest-proof)))
   (app (function/const* 'signed/all-at-most-empty [zero-level]) nat f g)
   (reverse (range index-count))))

(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rnum [v] (app (function/const* 'nnrat/numerator []) v))
(defn- rden [v] (app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))

(defn- computed-equivalence
  "Both sides reduce to concrete pairs, so the cross product of the equivalence
  is an identity between two numerals."
  [left right]
  (app (function/const* 'equality/reflexive [type-level]) nat
       (nmul (rnum (radd (pos left) (neg right)))
             (rden (radd (pos right) (neg left))))))

;; ---- the instance ------------------------------------------------------------

(defn- candidate-binders
  "The binders of a statement about EVERY feasible, nonnegative candidate plan."
  [{:keys [b rows cols row-activity zero-on]}]
  [['candidate (function/arrow nat signed)]
   ['candidate-feasible (all-at-most (row-activity 'candidate) b rows)]
   ['candidate-nonnegative (all-at-most (zero-on) 'candidate cols)]])

(defn- instance-terms [{:keys [matrix capacities margins plan prices]}]
  (let [row-count (count capacities)
        column-count (count margins)
        signed-vector (fn [values] (nat-lookup signed (mapv signed-literal values)))
        M (nat-lookup (function/arrow nat signed)
                      (mapv signed-vector matrix))
        b (signed-vector capacities)
        c (signed-vector margins)
        x (signed-vector plan)
        y (signed-vector prices)
        rows (index-list row-count)
        cols (index-list column-count)
        row-activity (fn [f]
                       (function/lam
                        [['i nat]]
                        (map-sum (function/lam [['j nat]]
                                               (smul (app (app M 'i) 'j)
                                                     (app f 'j)))
                                 cols)))
        dual-price (function/lam
                    [['j nat]]
                    (map-sum (function/lam [['i nat]]
                                           (smul (app (app M 'i) 'j)
                                                 (app y 'i)))
                             rows))
        zero-on (fn [] (function/lam [['ignored nat]] signed-zero))
        objective (fn [f]
                    (map-sum (function/lam [['j nat]]
                                           (smul (app c 'j) (app f 'j)))
                             cols))]
    {:M M :b b :c c :x x :y y :rows rows :cols cols
     :row-count row-count :column-count column-count
     :row-activity row-activity :dual-price dual-price
     :zero-on zero-on :objective objective
     :dual-objective (map-sum (function/lam [['i nat]]
                                            (smul (app b 'i) (app y 'i)))
                              rows)}))

(defn- objective-value [{:keys [margins plan]}]
  (reduce + 0 (map * (map rationalize margins) (map rationalize plan))))

;; ---- problem sense ----------------------------------------------------------
;;
;; The theorems are stated for `maximize margins . plan subject to
;; matrix * plan <= capacities`. A cost problem is the same problem with the
;; objective negated, which is ordinary data here rather than a second theorem,
;; because signed coefficients are already the norm. A COVERING constraint
;; `a . x >= v` is likewise `(-a) . x <= -v`; the caller writes it that way and
;; nothing downstream changes.

(defn- minimizing? [instance] (= :minimize (:sense instance)))

;; An EQUALITY row a . x = v is the pair a . x <= v and (-a) . x <= -v, and its
;; dual price is FREE rather than nonnegative. Splitting the free price p into
;; max(p,0) and max(-p,0) gives the two nonnegative prices the theorems require
;; while reproducing the free-dual semantics exactly: the contribution to column
;; j is a_j*y+ + (-a_j)*y- = a_j*(y+ - y-) = a_j*p, and to the dual objective
;; v*y+ + (-v)*y- = v*p.
(defn- expand-equalities
  [{:keys [equalities equality-prices matrix capacities prices] :as instance}]
  (if (empty? equalities)
    instance
    (do
      (when-not (= (count equalities) (count equality-prices))
        (throw (ex-info "Every equality needs exactly one free dual price"
                        {:error/category :lp-certificate/equality-price-mismatch
                         :equalities (count equalities)
                         :equality-prices (count equality-prices)})))
      (let [rows (mapcat (fn [{:keys [row]}] [(vec row) (mapv - row)]) equalities)
            values (mapcat (fn [{:keys [value]}] [value (- value)]) equalities)
            split (mapcat (fn [price]
                            (let [p (rationalize price)]
                              [(max p 0) (max (- p) 0)]))
                          equality-prices)]
        (-> instance
            (assoc :matrix (into (vec matrix) rows)
                   :capacities (into (vec capacities) values)
                   :prices (into (vec prices) split))
            (dissoc :equalities :equality-prices))))))

(defn- standard-form
  "The maximization instance over `<=` rows that the theorems are proved about."
  [instance]
  (let [expanded (expand-equalities instance)]
    (if (minimizing? expanded)
      (update expanded :margins #(mapv - %))
      expanded)))

;; ---- predicting cost before paying it ---------------------------------------
;;
;; `signed/decide-at-most a b` reduces to a nat comparison of the cross products
;; num_L * den_R and num_R * den_L, and naturals are unary, so what a comparison
;; COSTS is governed by the magnitude of those products. Mirroring the kernel's
;; nnrat arithmetic here -- crucially WITHOUT reducing to lowest terms, which the
;; kernel never does -- predicts that magnitude from instance data alone, with no
;; kernel and no JVM work.
;;
;; Denominators need no special case. Summing n terms multiplies their
;; denominators, so fractional data grows as d^n on its own. That is not a corner
;; case: two fractional prices in a nine-row instance raise the compared
;; magnitude 363-fold, which is what actually puts an instance out of reach.
;; Measured cost tracks `terms * magnitude` to within about 8% across a
;; thirty-fold range, and over-predicts real instances by roughly 1.6x.

(def ^:private refusal-margin
  "How far past the budget an estimate must be before it is treated as decisive.
  Chosen from measurement, not taste: see the verdict comment in `preflight`."
  50)

(def ^:private cost-per-unit-magnitude
  "Calibrated on a family with known exact duals, then checked against the
  worked instances in the test suite. Deliberately an OVER-estimate."
  2400)

(defn- q-add [[n1 d1] [n2 d2]] [(+ (* n1 d2) (* n2 d1)) (* d1 d2)])
(defn- q-mul [[n1 d1] [n2 d2]] [(* n1 n2) (* d1 d2)])
(defn- g-add [[p1 n1] [p2 n2]] [(q-add p1 p2) (q-add n1 n2)])
(defn- g-mul [[p1 n1] [p2 n2]]
  [(q-add (q-mul p1 p2) (q-mul n1 n2)) (q-add (q-mul p1 n2) (q-mul n1 p2))])

(defn- g-of [value]
  (let [[n d] (rational-parts value)]
    (if (neg? n) [[0 d] [(- n) d]] [[n d] [0 d]])))

(def ^:private g-zero [[0 1] [0 1]])
(defn- g-sum [xs] (reduce g-add g-zero xs))

(defn- cross-magnitude
  "The larger of the two nat products `signed/decide-at-most` multiplies."
  [[pa na] [pb nb]]
  (let [[ln ld] (q-add pa nb)
        [rn rd] (q-add pb na)]
    (max (* ln rd) (* rn ld))))

(defn preflight
  "Estimate the most expensive single normalization the certificate will need.

  The kernel spends its budget PER NORMALIZATION, so this -- not the total --
  is what the ceiling bites on. Returns the estimate, the budget it was compared
  against, and whether the instance is predicted to fit. Costs no kernel work,
  so it is safe to call before deciding whether to try."
  ([instance] (preflight instance kernel/*reduction-budget*))
  ([instance budget]
   (let [{:keys [matrix capacities margins plan prices]} (standard-form instance)
         M (mapv #(mapv g-of %) matrix)
         b (mapv g-of capacities) c (mapv g-of margins)
         x (mapv g-of plan) y (mapv g-of prices)
         rows (count capacities) cols (count margins)
         magnitudes
         (concat
          (for [i (range rows)]
            (cross-magnitude (g-sum (for [j (range cols)]
                                      (g-mul (get-in M [i j]) (nth x j))))
                             (nth b i)))
          (for [j (range cols)]
            (cross-magnitude (nth c j)
                             (g-sum (for [i (range rows)]
                                      (g-mul (get-in M [i j]) (nth y i))))))
          [(cross-magnitude (g-sum (for [j (range cols)] (g-mul (nth c j) (nth x j))))
                            (g-sum (for [i (range rows)] (g-mul (nth b i) (nth y i)))))])
         worst (apply max magnitudes)
         terms (max rows cols)
         estimate (* cost-per-unit-magnitude terms worst)]
     {:worst-magnitude worst
      :terms terms
      :estimated-reductions estimate
      :budget budget
      ;; The model is calibrated, not exact, and it OVER-predicts: the portfolio
      ;; instance in the test suite checks comfortably at the default budget yet
      ;; estimates 4.6x over it. Refusing an instance that would really check is
      ;; far worse than letting a doomed one grind, so :over-budget is reserved
      ;; for a miss of fifty-fold or more. That still separates cleanly --
      ;; instances that genuinely check estimate at most ~5x over, while the
      ;; fractional ones estimate 235x, 5662x and 10^10x over -- with two orders
      ;; of magnitude of headroom on each side.
      :verdict (cond (< estimate budget) :fits
                     (< estimate (* refusal-margin budget)) :marginal
                     :else :over-budget)})))

;; ---- removing denominators before they multiply -----------------------------
;;
;; Fractional data, not size, is what puts instances out of reach (see the cost
;; model above: unreduced denominators grow as d^n).
;;
;; Scaling the instance to integers removes that entirely, and it is EXACT
;; rather than approximate. With D the lcm of every denominator present, scale
;; the matrix, plan and prices by D, and the capacities and margins by D^2:
;;
;;   primal    A x <= b        becomes  (DA)(Dx) <= D^2 b    -- both sides * D^2
;;   dual      A' y >= c       becomes  (DA)'(Dy) >= D^2 c   -- both sides * D^2
;;   objective c . x <= b . y  becomes  D^3 (c . x) <= D^3 (b . y)
;;
;; Both sides of the objective comparison scale by the SAME D^3, so the proved
;; relation is the original one and the reported numbers divide back exactly.
;; The certificate is then a statement about the scaled data, which is why the
;; scale factor is reported rather than hidden.

(defn- denominator-of [value] (second (rational-parts value)))

(defn integer-scale
  "The lcm of every denominator in the instance; 1 when the data is integral.

  Returns a plain integer deliberately. Computing it through `biginteger` yields
  a BigInt, and a BigInt coefficient is numerically equal to the Long it came
  from but SERIALIZES DIFFERENTLY -- which silently changes the content id, and
  so silently broke the property that scaling integral data leaves its identity
  alone."
  [{:keys [matrix capacities margins plan prices equalities equality-prices]}]
  (long
   (reduce (fn [acc value]
             (let [d (denominator-of value)]
               (/ (* acc d) (.gcd (biginteger acc) (biginteger d)))))
           1
           ;; equality rows/values and free prices carry denominators too; omitting
           ;; them leaves D too small to clear a fractional equality, so the
           ;; "integerized" instance is not actually integral -- see integerize.
           (concat (apply concat matrix) capacities margins plan prices
                   (mapcat :row equalities)
                   (map :value equalities)
                   equality-prices))))

(defn integerize
  "Rescale to integer data, returning the instance and the scale used.

  A no-op on integral data -- scale 1 leaves every coefficient identical, so an
  already-integral instance produces the same proof term and the same audit id."
  [instance]
  (let [d (integer-scale instance)
        dd (* d d)
        by (fn [k] (partial mapv (fn [v] (* (rationalize v) k))))]
    (if (= 1 d)
      ;; not merely "multiplies by one" -- returns the very same value, so the
      ;; proof term and audit id are identical rather than merely equivalent
      [instance 1]
      [(cond-> (-> instance
                   (update :matrix (partial mapv (by d)))
                   (update :capacities (by dd))
                   (update :margins (by dd))
                   (update :plan (by d))
                   (update :prices (by d)))
         ;; Equalities must scale too, or the scaled kernel check runs on
         ;; inconsistent data while the inequality part is scaled. expand-equalities
         ;; turns each {:row a :value v} with free price p into matrix rows +-a
         ;; (scale d, like :matrix), capacities +-v (scale dd, like :capacities)
         ;; and prices max(p,0)/max(-p,0) (scale d, like :prices) -- so :row scales
         ;; by d, :value by dd, and :equality-prices by d, identically.
         (seq (:equalities instance))
         (update :equalities
                 (partial mapv #(-> % (update :row (by d)) (update :value (fn [v] (* (rationalize v) dd))))))
         (seq (:equality-prices instance))
         (update :equality-prices (by d)))
       d])))

(defn- reported
  "Translate the standard-form numbers back into the caller's sense. For a cost
  problem the proved quantity is a LOWER bound: no feasible plan costs less."
  [instance achieved proved]
  (if (minimizing? instance)
    {:achieved (- achieved) :bound (- proved) :direction :lower
     :gap (- achieved proved)}
    {:achieved achieved :bound proved :direction :upper
     :gap (- proved achieved)}))

(defn certificate-spec
  "The proof data asserting that no feasible plan beats `plan`.

  With {:proof :reflection} the statement is the same and the proof is one
  application of `lp/certificate-check-sound` to the data and `refl true`: the
  kernel runs the certificate checker instead of reading one proof per row and
  column. The default proof composes those per-row proofs, as it always has."
  ([alias instance] (certificate-spec alias instance nil))
  ([alias instance {:keys [proof]}]
  (let [{:keys [M b c x y rows cols row-count column-count
                row-activity dual-price zero-on objective dual-objective]
         :as terms}
        (instance-terms instance)]
    {:name alias :universes []
     :type
     (function/forall
      (candidate-binders terms)
      (sle (map-sum (function/lam [['j nat]]
                                  (smul (app c 'j) (app 'candidate 'j)))
                    cols)
           (objective x)))
     :value
     (if (= :reflection proof)
       (app (function/const* 'lp/certificate-check-sound [zero-level])
            nat nat M b c x y rows cols
            (app (function/const* 'equality/reflexive [type-level]) bool bool-true))
     (function/lam
      (candidate-binders terms)
      (app (function/const*
            'optimization/signed-lp-optimality-certificate-on [zero-level])
           nat nat M b c x y rows cols
           (all-at-most-proof (row-activity x) b row-count)
           (all-at-most-proof c dual-price column-count)
           (all-at-most-proof (zero-on) x column-count)
           (all-at-most-proof (zero-on) y row-count)
           (computed-equivalence dual-objective (objective x))
           'candidate 'candidate-feasible 'candidate-nonnegative)))})))

(defn value-spec
  "The proof data asserting the certified objective equals a stated number."
  [alias instance]
  (let [{:keys [x objective]} (instance-terms instance)
        value (objective-value instance)
        stated (signed-literal value)]
    {:name alias :universes []
     :type (seq-equiv (objective x) stated)
     :value (computed-equivalence (objective x) stated)}))

(defn- predicted-refusal
  "A refusal built from the cost model, or nil to go ahead and check.

  Only a WIDE miss short-circuits. The model is calibrated rather than exact --
  it OVER-predicts, by up to about 5x on instances that really check -- so
  anything within fifty-fold of the budget is handed to the kernel, which is the
  authority. What this catches is
  the case that is not close: a fractional instance predicted in the billions,
  where the kernel would otherwise spend a minute or more per comparison
  exhausting the budget before refusing anyway.

  The refusal names the scale factor `integerize` would use, because for
  fractional data that is usually the fix rather than a bigger budget. Only integral
  data is ever refused (see below), so that scale is always 1."
  [instance reductions preflight?]
  (when preflight?
    (let [estimate (preflight instance reductions)
          scale (integer-scale instance)]
      ;; ONLY INTEGRAL DATA MAY BE REFUSED.
      ;;
      ;; The model computes the UNREDUCED cross product, so a denominator d over
      ;; n terms contributes d^n to its estimate -- but the kernel's real cost
      ;; does not grow that way. Measured: a three-variable instance with
      ;; denominator 2 estimates 3.3 BILLION and the kernel checks it in 151s,
      ;; an over-prediction of some three thousand fold. On integral data the
      ;; same model is out by only 4x to 9x.
      ;;
      ;; A false refusal is worse than a slow one: it withholds a certificate the
      ;; kernel would have issued. So on fractional data the estimate is reported
      ;; and never acted on, and the kernel decides.
      (when (and (= 1 scale) (= :over-budget (:verdict estimate)))
        {:status :rejected
         :error/category :lp-certificate/predicted-over-budget
         :message (str "Predicted cost " (:estimated-reductions estimate)
                       " far exceeds the reduction budget " reductions
                       ". Raise :reductions, or reduce coefficient magnitudes.")
         :preflight estimate
         :integer-scale scale}))))

(defn bound-spec
  "The proof data asserting that no feasible plan scores above the dual bound.

  This is the assurance level a partial solve can still reach: it needs the plan
  to be feasible and the prices to be dual feasible, but NOT the gap to be
  closed. A buyer who cannot solve to optimality still learns a number no plan
  can beat."
  [alias instance]
  (let [{:keys [M b c x y rows cols row-count column-count
                row-activity dual-price zero-on objective dual-objective]}
        (instance-terms instance)]
    {:name alias :universes []
     :type (sle (objective x) dual-objective)
     :value
     (app (function/const* 'optimization/signed-lp-weak-duality-on [zero-level])
          nat nat M b c x y rows cols
          (all-at-most-proof (row-activity x) b row-count)
          (all-at-most-proof c dual-price column-count)
          (all-at-most-proof (zero-on) x column-count)
          (all-at-most-proof (zero-on) y row-count))}))

(defn universal-bound-spec
  "The proof data asserting that NO feasible plan scores above the dual bound --
  not merely the one that was submitted.

  This is the statement an integer program needs. Every integral plan is in
  particular a feasible plan, so a bound proved over all feasible plans prunes
  the whole branch-and-bound subtree below it. Nothing here mentions
  integrality: the relaxation bound holds because the integral plans are a
  SUBSET of the plans the theorem already quantifies over."
  [alias instance]
  (let [{:keys [M b c y rows cols row-count column-count
                dual-price zero-on objective dual-objective]
         :as terms}
        (instance-terms instance)]
    {:name alias :universes []
     :type (function/forall (candidate-binders terms) (sle (objective 'candidate) dual-objective))
     :value
     (function/lam
      (candidate-binders terms)
      (app (function/const* 'optimization/signed-lp-weak-duality-on [zero-level])
           nat nat M b c 'candidate y rows cols
           'candidate-feasible
           (all-at-most-proof c dual-price column-count)
           'candidate-nonnegative
           (all-at-most-proof (zero-on) y row-count)))}))

;; ---- scaling bridge (DRAFT, path (a): per-listed-index equivalence fold) -----
;;
;; With integerize? true the kernel checks bound-spec on the SCALED instance:
;; `sle (objective x_s) dual-objective_s`, where the scaled coefficients are baked
;; into signed LITERALS. signed/lp-scaled-objectives-bound transports a
;; bound between FORMAL D^2/D-scaled objectives to the original -- but its premise
;; `checked-left` is `map-sum (\i. multiply (scale D^2 (c i)) (scale D (x i)))`,
;; NOT the literal-baked scaled objective. They are equivalent but NOT
;; definitionally equal (a symbolic-index lambda mismatch; measured :rejected on a
;; direct feed). This fold builds the explicit equivalence per listed index and
;; transports the checked scaled bound into premise, then applies the
;; theorem to certify the ORIGINAL bound-spec over the actual host terms.
;;
;; STATUS (measured 2026-09-10): correct and tamper-evident at one dimension, but
;; past one dimension the per-index scale-of-lookup reductions exhaust the default
;; budget (2 columns: ~22s, :kernel/resource-limit). So this is EXPERIMENTAL and NOT
;; wired into `bound`; rainbow.math.rational.signed.lp-pointwise-bridge replaces the fold.
;; Measurements: the design notes ("IMPLEMENTED + MEASURED").

(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- signed-scale [d v] (app (function/const* 'signed/scale []) d v))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- coefficient-of
  ;; the positive rational D = (ap+1)/(adp+1); a whole D is (numeral (dec D))+1 / 1
  [D]
  (app (function/const* 'nnrat/make []) (numeral D) (numeral 0)))
(defn- add-respects [a ah b bh sa sb]
  (app (function/const* 'signed/add-respects-equivalence []) a ah b bh sa sb))
(defn- at-most-respects [a ah b bh sa sb ordered]
  (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh sa sb ordered))
(defn- signed-equiv-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- equiv-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))

;; equivalent (map-sum f idxs) (map-sum g idxs), given per-index equivalences.
;; Recurses over the concrete index list, keeping each level's type SYNTACTICALLY
;; in map-sum form so every defeq the kernel performs is only ONE cons deep. A
;; plain outward fold accumulates nested sadd on one side while the goal stays in
;; map-sum form, forcing a full-depth reduction that exhausts the budget on real
;; (lookup + scale + nnrat) endpoints past one dimension. Here each step wraps the
;; add-congruence between the two shallow map-sum-cons unfoldings.
(defn- mapsum-corresponds
  [f g per-index index-count]
  (letfn [(build [idx]
            (if (>= idx index-count)
              ;; nil tail: map-sum f nil defeq map-sum g nil defeq signed-zero
              (signed-equiv-refl (map-sum f (index-range index-count index-count)))
              (let [k (numeral idx)
                    rest (index-range (inc idx) index-count)
                    ms-f-cons (map-sum f (index-range idx index-count))
                    ms-g-cons (map-sum g (index-range idx index-count))
                    ms-f-rest (map-sum f rest) ms-g-rest (map-sum g rest)
                    fk (app f k) gk (app g k)
                    ;; inner : equiv (sadd fk ms-f-rest) (sadd gk ms-g-rest)
                    inner (add-respects fk gk ms-f-rest ms-g-rest
                                        (per-index idx) (build (inc idx)))]
                ;; ms-f-cons defeq (sadd fk ms-f-rest) and (sadd gk ms-g-rest)
                ;; defeq ms-g-cons -- both one cons deep -- so this yields the
                ;; exact map-sum-form equivalence.
                (equiv-trans ms-f-cons (sadd gk ms-g-rest) ms-g-cons
                             inner (signed-equiv-refl ms-g-cons)))))]
    (build 0)))

;; A scaled-side term `smul (c_s k)(x_s k)` and formal
;; `smul (scale D^2 (c k))(scale D (x k))` reduce to the same concrete signed
;; value, so a computed-equivalence discharges each listed index.
(defn- transported-bound-spec
  "DRAFT. Certify the ORIGINAL bound-spec via scaled-objectives bound,
  linking the literal-baked scaled endpoints to the formal scaled endpoints by a
  per-listed-index equivalence fold. `orig`/`scaled` are standard-form instances;
  D>1 is the integer scale."
  [alias orig scaled D]
  (let [ot (instance-terms orig)
        st (instance-terms scaled)
        {:keys [c x b y cols rows objective dual-objective
                column-count row-count]} ot
        d (coefficient-of D)
        d2 (rmul d d)
        ;; runtime scaled endpoints (literal-baked), as in bound-spec on `scaled`
        f-obj (function/lam [['j nat]] (smul (app (:c st) 'j) (app (:x st) 'j)))
        f-dual (function/lam [['i nat]] (smul (app (:b st) 'i) (app (:y st) 'i)))
        ;; formal scaled endpoints over the ORIGINAL lookup functions
        g-obj (function/lam [['j nat]] (smul (signed-scale d2 (app c 'j))
                                             (signed-scale d (app x 'j))))
        g-dual (function/lam [['i nat]] (smul (signed-scale d2 (app b 'i))
                                              (signed-scale d (app y 'i))))
        L-s (map-sum f-obj cols)   checked-left  (map-sum g-obj cols)
        R-s (map-sum f-dual rows)  checked-right (map-sum g-dual rows)
        per-index (fn [lam-f lam-g]
                    (fn [k] (computed-equivalence (app lam-f (numeral k))
                                                  (app lam-g (numeral k)))))
        obj-eq  (mapsum-corresponds f-obj g-obj  (per-index f-obj g-obj)  column-count)
        dual-eq (mapsum-corresponds f-dual g-dual (per-index f-dual g-dual) row-count)
        scaled-bound (:value (bound-spec 'optimization/scaling-bridge-scaled scaled))
        premise (at-most-respects L-s checked-left R-s checked-right obj-eq dual-eq scaled-bound)
        transported
        (app (function/const* 'signed/lp-scaled-objectives-bound [zero-level])
             nat (numeral (dec D)) (numeral 0)
             c x b y cols rows premise)]
    {:name alias :universes []
     :type (sle (objective x) dual-objective)
     :value transported}))

(defn- dual-value [{:keys [capacities prices]}]
  (reduce + 0 (map * (map rationalize capacities) (map rationalize prices))))

(defn- audit-identity
  "A content-addressed identity for the whole check: the exact instance, the
  declarations that were checked, and their axiom closures. Two runs on the same
  data produce the same id, and any change to the data changes it."
  [instance verdicts]
  (canonical/content-id
   {:instance instance
    :declarations (into (sorted-map)
                        (map (fn [[name verdict]]
                               [(str name) (select-keys verdict [:id :status])]))
                        verdicts)}))

(defn- run-specs [checked-environment instance specs]
  (let [environment (support/extend-with checked-environment :lp-certificate specs)
        ids (support/spec-ids environment specs)
        verdicts
        (into (sorted-map)
              (map (fn [[name id]]
                     (let [declaration (environment/declaration environment id)]
                       [name {:id id
                              :status (:status
                                       (kernel/check
                                        environment
                                        (:rainbow/value declaration)
                                        (:rainbow/type declaration)
                                        (set (:rainbow/universes declaration))))
                              :axioms (kernel/axioms environment id)}])))
              ids)]
    {:verdicts verdicts :environment environment}))

(defn audit-bundle
  "The serializable record of a check, for someone who was not there.

  A hash alone is not provenance: it pins WHICH numbers were checked but says
  nothing about what was concluded or on what it rested. The bundle carries the
  exact instance, the verdict, every declaration id with its kernel status and
  axiom closure, and the environment the check ran against, so a reader can
  re-derive the identity and confirm the axiom closures are empty rather than
  take either on trust. It contains no proof terms and no live objects, so it
  can be written to disk and read back."
  [result environment-id]
  (-> result
      (dissoc :environment)
      (assoc :audit/environment-id environment-id
             :audit/schema-version schema-version)))

(defn- construction-rejected [exception]
  (let [data (ex-data exception)]
    {:status :rejected
     :error/category (:error/category data :lp-certificate/construction-failed)
     :message (.getMessage exception)
     ;; the useful category is usually the kernel's, nested inside the
     ;; declaration rejection; dropping it makes every refusal look alike
     :kernel/category (get-in data [:result :error :cause :error :error/category]
                              (get-in data [:result :error :error/category]))
     :data data}))

(defn bound
  "Kernel-checks that no feasible plan scores above `capacities . prices`.

  Unlike `certify` this does NOT require the gap to be closed, so it applies to a
  plan from a truncated or heuristic solve. The reported `:gap` is the distance
  from the achieved value to the proved bound -- the quality guarantee a buyer
  can act on."
  ([checked-environment instance] (bound checked-environment instance nil))
  ([checked-environment instance
    {:keys [alias reductions preflight? integerize?]
     :or {alias 'optimization/lp-instance-bound
          reductions kernel/*reduction-budget*
          preflight? true
          integerize? false}}]
   (try
     (binding [kernel/*reduction-budget* reductions]
     ;; When asked to integerize, the KERNEL CHECKS THE SCALED INSTANCE -- a
     ;; genuinely different proof about genuinely different data -- while the
     ;; numbers reported back are computed from the ORIGINAL, so the caller reads
     ;; a bound in their own units rather than in units of D^3.
       (let [[checked scale] (if integerize? (integerize instance) [instance 1])]
         (if-let [refusal (predicted-refusal checked reductions preflight?)]
       ;; predicted-refusal reports the scale OF THE INSTANCE IT SAW, which is
       ;; the actionable number; the outer scale would overwrite it with 1
           refusal
           (let [standard (standard-form checked)
                 original (standard-form instance)
                 specs [(bound-spec alias standard)
                        (universal-bound-spec
                         (symbol (namespace alias) (str (name alias) "-universal"))
                         standard)]
                 {:keys [verdicts]} (run-specs checked-environment standard specs)
                 numbers (reported instance
                                   (objective-value original)
                                   (dual-value original))]
             (merge
              {:status (if (every? #(= :checked (:status %)) (vals verdicts))
                         :bounded :rejected)
               :instance instance
               :sense (if (minimizing? instance) :minimize :maximize)
               :rows (count (:capacities instance))
               :columns (count (:margins instance))
               :reductions reductions
         ;; the audit chain: what was checked, and what it was derived from.
         ;; The id necessarily identifies the SCALED check when scaling happened
         ;; -- that is what the kernel actually accepted -- so the scale and the
         ;; checked instance are recorded beside it rather than hidden.
               :integer-scale scale
               :instance/checked checked
               :declarations verdicts
               :audit/id (audit-identity checked verdicts)}
              numbers)))))
     (catch clojure.lang.ExceptionInfo exception
       (construction-rejected exception)))))

(defn certify
  "Kernel-checks that `plan` is optimal for the instance, with `prices` as the
  dual certificate.

  The instance is `{:matrix [[..]] :capacities [..] :margins [..] :plan [..]
  :prices [..]}` over any Clojure rationals, negative included, for the program
  `maximize margins . plan subject to matrix * plan <= capacities, plan >= 0`."
  ([checked-environment instance] (certify checked-environment instance nil))
  ([checked-environment instance
    {:keys [alias reductions preflight? proof table]
     :or {alias 'optimization/lp-instance-optimal
          reductions kernel/*reduction-budget*
          preflight? true}}]
   (try
     (binding [kernel/*reduction-budget* reductions
               *table-encoding* (or table :linear)]
       (if-let [refusal (predicted-refusal instance reductions preflight?)]
         refusal
         (let [standard (standard-form instance)
               ;; a reflective certificate needs the checker and its soundness theorem
               checked-environment (if (= :reflection proof)
                                     (module/install-module checked-environment
                                                            'rainbow.math.rational.signed.lp-certificate-reflect)
                                     checked-environment)
               specs [(certificate-spec alias standard {:proof proof})
                      (value-spec (symbol (namespace alias)
                                          (str (name alias) "-value"))
                                  standard)]
               {:keys [verdicts environment]}
               (run-specs checked-environment standard specs)]
           {:status (if (every? #(= :checked (:status %)) (vals verdicts))
                      :certified :rejected)
            :instance instance
            :sense (if (minimizing? instance) :minimize :maximize)
            :objective (:achieved (reported instance (objective-value standard)
                                            (dual-value standard)))
            :rows (count (:capacities instance))
            :columns (count (:margins instance))
            :reductions reductions
            :declarations verdicts
            :audit/id (audit-identity instance verdicts)
            :proof (or proof :composed)
            ;; the modules a bundle of this certificate must install on its base
            :bundle/modules (cond-> '[rainbow.math.rational.signed.lp-duality-on rainbow.math.rational.signed.decide-order]
                              (= :reflection proof) (conj 'rainbow.math.rational.signed.lp-certificate-reflect))
            :environment environment})))
     (catch clojure.lang.ExceptionInfo exception
       (construction-rejected exception)))))
