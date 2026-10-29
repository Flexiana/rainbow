(ns rainbow.math.rational.signed.lp-minimization-bridge
  "Instance-specific translation evidence for actual minimization coefficient tables.
  Proves correspondence for EVERY Nat index, then every candidate objective and
  a universal lower bound expressed with original costs. Existing standard-form
  constraint/equality expansion and literal interpretation remain host boundaries."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-objective-negate :as sense]
            [rainbow.math.rational.signed.lp-witness-bridge :as witness]
            [rainbow.math.rational.signed.multiply-ring :as multiply]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- neg [x] (app 'signed/negate x))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- mapping [values] (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal values)))
(defn- sum [m indices] (poly 'signed/map-sum lp/nat m indices))
(defn- all-le [l r indices] (poly 'signed/all-at-most lp/nat l r indices))

(defn coefficient-negation-spec
  "Proof spec for supplied ACTUAL and ORIGINAL tables, not an ideal replacement.
  False coefficient correspondences must be rejected by the kernel. The terminal
  entry repeats past the table exactly as the runtime lookup does. Shape errors
  are host refusals; proof construction alone certifies no arithmetic relation."
  [actual original]
  (when-not (and (vector? actual) (vector? original) (seq actual)
                 (= (count actual) (count original)))
    (throw (ex-info "Expected nonempty equally sized coefficient vectors"
                    {:error/category :lp-minimization/table-shape})))
  (let [a (mapping actual) o (mapping original)
        at (fn [i] (eqv (f/app a i) (neg (f/app o i))))
        leaf (fn [i] (#'lp/computed-equivalence (f/app a i) (neg (f/app o i))))]
    {:type (f/forall [['index lp/nat]] (at 'index))
     :value
     (if (= 1 (count actual))
       (f/lam [['index lp/nat]] (leaf 'index))
       (let [tail (:value (coefficient-negation-spec (subvec actual 1) (subvec original 1)))]
         (f/lam
          [['index lp/nat]]
          (f/app (f/const* 'data/Nat.rec [[:zero]])
                 (f/lam [['i lp/nat]] (at 'i)) (leaf (#'lp/numeral 0))
                 (f/lam [['predecessor lp/nat] ['ignored (at 'predecessor)]]
                        (f/app tail 'predecessor)) 'index))))}))

(defn minimization-specs
  "Produce actual-table, arbitrary-candidate objective and original-cost bound specs.
  Uses the standardizer's literal table as the left endpoint. The original cost
  coefficients are retained separately and never substituted by negated originals
  on that left endpoint. A supplied lower bound is supported through the existing
  exact-dual-endpoint witness producer. Not a verified implementation of mapv -,
  and not a complete LP certificate (submitted-plan feasibility is separate)."
  [instance lower]
  (when-not (= :minimize (:sense instance))
    (throw (ex-info "This producer requires a minimization instance"
                    {:error/category :lp-minimization/wrong-sense})))
  (let [standard (#'lp/standard-form instance)
        st (#'lp/instance-terms standard)
        original-cost-data (assoc standard :margins (:margins instance))
        ot (#'lp/instance-terms original-cost-data)
        nc (f/lam [['i lp/nat]] (neg (f/app (:c ot) 'i)))
        table (coefficient-negation-spec (:margins standard) (:margins instance))
        original-obj ((:objective ot) 'candidate)
        actual-products (f/lam [['i lp/nat]]
                               (app 'signed/multiply (f/app (:c st) 'i) (f/app 'candidate 'i)))
        formal-products (f/lam [['i lp/nat]]
                               (app 'signed/multiply (f/app nc 'i) (f/app 'candidate 'i)))
        actual-obj (sum actual-products (:cols ot))
        formal-obj (sum formal-products (:cols ot))
        pointwise (f/lam [['i lp/nat]]
                         (app 'signed/multiply-right-respects-equivalence
                              (f/app (:c st) 'i) (f/app nc 'i) (f/app 'candidate 'i)
                              (f/app (:value table) 'i)))
        correspondence (poly 'signed/map-sum-respects-equivalence lp/nat
                             actual-products formal-products pointwise (:cols ot))
        candidate [['candidate (f/arrow lp/nat lp/signed)]]
        bindings (into candidate
                       [['feasible (all-le ((:row-activity ot) 'candidate) (:b ot) (:rows ot))]
                        ['nonnegative (all-le ((:zero-on ot)) 'candidate (:cols ot))]])
        ;; Validate the reported endpoint before passing it to the literal encoder.
        universal (:universal-reported-bound (witness/witness-specs instance lower))
        lower-term (#'lp/signed-literal lower)
        actual-endpoint (#'lp/signed-literal (- lower))
        upper (f/app (:value universal) 'candidate 'feasible 'nonnegative)
        formal-upper (app 'signed/at-most-respects-equivalence
                          actual-obj formal-obj actual-endpoint (neg lower-term)
                          correspondence
                          (#'lp/computed-equivalence actual-endpoint (neg lower-term)) upper)]
    (array-map
     :coefficient-negation table
     :candidate-objective-negation
     {:type (f/forall candidate (eqv actual-obj (neg original-obj)))
      :value (f/lam candidate
                    (app 'signed/equivalent-transitive actual-obj formal-obj (neg original-obj)
                         correspondence
                         (poly 'signed/lp-objective-negate lp/nat (:c ot) 'candidate (:cols ot))))}
     :universal-original-lower-bound
     {:type (f/forall bindings (app 'signed/at-most lower-term original-obj))
      :value (f/lam bindings
                    (poly 'signed/lp-negated-objective-bound-to-lower lp/nat
                          (:c ot) 'candidate (:cols ot) lower-term formal-upper))})))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-witness-bridge rainbow.math.rational.signed.lp-objective-negate rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-minimization-bridge))
