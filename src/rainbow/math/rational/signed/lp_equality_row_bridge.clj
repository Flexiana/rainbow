(ns rainbow.math.rational.signed.lp-equality-row-bridge
  "Instance evidence relating supplied actual expanded rows/RHS to an original
  equality. Untrusted producer, not a complete standardizer or verifier proof."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-equality-row-transport :as transport]
            [rainbow.math.rational.signed.lp-minimization-bridge :as minimization]
            [rainbow.or.lp-certificate :as lp]))

(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(defn- eqv [a b] (app 'signed/equivalent a b))
(defn- neg [v] (app 'signed/negate v))
(defn- bounded? [x]
  (and (or (integer? x) (ratio? x))
       (<= -10000 (if (ratio? x) (numerator x) x) 10000)
       (<= 1 (if (ratio? x) (denominator x) 1) 10000)))
(defn- mapping [xs]
  (if (seq xs) (#'lp/nat-lookup lp/signed (mapv #'lp/signed-literal xs))
      (f/lam [['index lp/nat]] (f/const* 'signed/zero []))))
(defn- same-table [actual original]
  (let [a (mapping actual) o (mapping original)
        at (fn [i] (eqv (f/app a i) (f/app o i)))
        leaf (fn [i] (#'lp/computed-equivalence (f/app a i) (f/app o i)))]
    {:type (f/forall [['index lp/nat]] (at 'index))
     :value
     (if (<= (count actual) 1)
       (f/lam [['index lp/nat]] (leaf 'index))
       (let [tail (:value (same-table (subvec actual 1) (subvec original 1)))]
         (f/lam [['index lp/nat]]
                (f/app (f/const* 'data/Nat.rec [[:zero]])
                       (f/lam [['i lp/nat]] (at 'i)) (leaf (#'lp/numeral 0))
                       (f/lam [['predecessor lp/nat] ['ignored (at 'predecessor)]]
                              (f/app tail 'predecessor)) 'index))))}))
(defn- negative-table [actual original]
  (if (seq original)
    (minimization/coefficient-negation-spec actual original)
    (let [a (mapping actual) o (mapping original)
          l (f/app a 'index) r (neg (f/app o 'index))]
      {:type (f/forall [['index lp/nat]] (eqv l r))
       :value (f/lam [['index lp/nat]] (#'lp/computed-equivalence l r))})))

(defn- validate-rows! [rows rhs-values]
  (when-not (and (every? vector? rows) (<= (count (first rows)) 32)
                 (apply = (map count rows)))
    (throw (ex-info "Expected equally sized row vectors of width <=32"
                    {:error/category :lp-equality-row/table-shape})))
  (when-not (every? bounded? (concat (mapcat identity rows) rhs-values))
    (throw (ex-info "Expected bounded exact row entries before literal encoding"
                    {:error/category :lp-equality-row/invalid-scalar}))))

(defn row-pair-specs
  "Return four actual-data correspondences and forall-candidate feasibility iff.
  Rows have equal width <=32, including empty rows; exact scalar bounds precede
  encoding. Actual entries are kept in the targets, not replaced by ideal rows.
  A caller must independently reconstruct targets and check every emitted proof."
  [original-row original-rhs positive-row positive-rhs negative-row negative-rhs]
  (validate-rows! [original-row positive-row negative-row]
                  [original-rhs positive-rhs negative-rhs])
  (let [o (mapping original-row) p (mapping positive-row) n (mapping negative-row)
        [b pb nb] (mapv #'lp/signed-literal [original-rhs positive-rhs negative-rhs])
        ps (same-table positive-row original-row)
        ns (negative-table negative-row original-row)
        pr {:type (eqv pb b) :value (#'lp/computed-equivalence pb b)}
        nr {:type (eqv nb (neg b)) :value (#'lp/computed-equivalence nb (neg b))}
        indices (#'lp/index-list (count original-row))
        obj (fn [a] (poly 'signed/map-sum lp/nat
                          (f/lam [['i lp/nat]]
                                 (app 'signed/multiply (f/app a 'i) (f/app 'candidate 'i))) indices))
        target (f/forall [['candidate (f/arrow lp/nat lp/signed)]]
                         (app 'proposition/equivalence (eqv (obj o) b)
                              (app 'proposition/conjunction (app 'signed/at-most (obj p) pb)
                                   (app 'signed/at-most (obj n) nb))))]
    (array-map
     :positive-coefficients ps :negative-coefficients ns
     :positive-rhs pr :negative-rhs nr
     :feasibility-equivalence
     {:type target
      :value (poly 'signed/lp-actual-equality-row-equivalence lp/nat o p n indices b pb nb
                   (:value ps) (:value ns) (:value pr) (:value nr))})))

(defn inequality-row-specs
  "Coefficient/RHS evidence and universal equivalence for an inequality prefix row."
  [original-row original-rhs actual-row actual-rhs]
  (validate-rows! [original-row actual-row] [original-rhs actual-rhs])
  (let [o (mapping original-row) a (mapping actual-row)
        [b ab] (mapv #'lp/signed-literal [original-rhs actual-rhs])
        same (same-table actual-row original-row)
        rhs {:type (eqv ab b) :value (#'lp/computed-equivalence ab b)}
        indices (#'lp/index-list (count original-row))
        dot (fn [m] (poly 'signed/map-sum lp/nat
                         (f/lam [['i lp/nat]] (app 'signed/multiply (f/app m 'i) (f/app 'candidate 'i))) indices))]
    {:coefficients same :rhs rhs
     :feasibility-equivalence
     {:type (f/forall [['candidate (f/arrow lp/nat lp/signed)]]
                      (app 'proposition/equivalence (app 'signed/at-most (dot o) b)
                           (app 'signed/at-most (dot a) ab)))
      :value (poly 'signed/lp-actual-inequality-row-equivalence lp/nat o a indices b ab
                   (:value same) (:value rhs))}}))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-equality-row-transport])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.lp-equality-row-bridge))
