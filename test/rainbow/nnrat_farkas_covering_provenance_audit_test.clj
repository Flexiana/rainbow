(ns rainbow.nnrat-farkas-covering-provenance-audit-test
  "Adversarial proof: cardinality covering does not preserve input constraints.

  A PASS records the weakness: an equal-length list of lower tautologies inhabits
  the covered partition conclusion for EVERY input and point, without the
  reduced-conditions premise. The alternate proof is checked against the shipped
  theorem's type. These audit declarations exist only in the test environment.
  When the statement gains provenance, rejection of this witness is good news:
  replace this known-gap regression with a rejection regression."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-partition-covered :as covered]
            [rainbow.math.rational.nnrat.farkas-partition-list :as partition]))

(def ^:private tl [:succ [:zero]])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(def ^:private R covered/nnrat)
(def ^:private N covered/nat)
(def ^:private ar covered/arow)
(def ^:private br covered/bs-row)
(def ^:private la covered/list-a)
(def ^:private lb covered/list-bs)
(def ^:private pair-lists covered/pair-lists)
(def ^:private z (c 'nnrat/zero))
(def ^:private nz (c 'data/zero))
(def ^:private trivial (c 'proposition/trivial))
(defn- nil-of [t] (f/app (f/const* 'data/nil [tl]) t))
(defn- cons-of [t h tail] (f/app (f/const* 'data/cons [tl]) t h tail))
(defn- pair [a b x y] (f/app (f/const* 'data/pair [tl tl]) a b x y))
(defn- first-of [pr] (f/app (f/const* 'product/first [tl tl]) la la pr))
(defn- second-of [pr] (f/app (f/const* 'product/second [tl tl]) la la pr))
(defn- conjp [a b] (app 'proposition/conjunction a b))
(defn- both [a b pa pb] (app 'proposition/conjoin a b pa pb))
(defn- left [a b h] (app 'proposition/left a b h))
(defn- right [a b h] (app 'proposition/right a b h))
(defn- length-of [t rows] (f/app (f/const* 'list/length [tl]) t rows))
(defn- neq [x y] (f/equality tl N x y))
(defn- refl [x] (f/app (f/const* 'equality/reflexive [tl]) N x))
(defn- lower-sat [rows w]
  (app 'nnrat/farkas-elim-affine-lower-rows-satisfied rows w))
(defn- upper-sat [rows w]
  (app 'nnrat/farkas-elim-affine-rows-satisfied rows w))
(defn- sat [pr w] (conjp (lower-sat (first-of pr) w) (upper-sat (second-of pr) w)))
(defn- count-sum [pr]
  (app 'algebra/nat-add (length-of ar (first-of pr)) (length-of ar (second-of pr))))
(defn- count-eq [pr rows] (neq (count-sum pr) (length-of br rows)))
(defn- pred [rows w]
  (f/lam [['pr pair-lists]] (conjp (sat 'pr w) (count-eq 'pr rows))))
(defn- goal [rows w]
  (f/app (f/const* 'proposition/existence [tl]) pair-lists (pred rows w)))
(defn- witness [rows w value evidence]
  (f/app (f/const* 'proposition/witness [tl]) pair-lists (pred rows w) value evidence))

;; A lower row (a,s,b) means b <= a*w+s. This row is true at every w.
(def ^:private tautology-row (pair R covered/p2 z (pair R R z z)))
(defn- tautology [w]
  (app 'nnrat/at-most z (app 'nnrat/add (app 'nnrat/multiply z w) z)))
(defn- tautology-proof [w]
  (app 'nnrat/zero-at-most (app 'nnrat/add (app 'nnrat/multiply z w) z)))

(def ^:private no-premise-spec
  {:name 'audit/farkas-covering-without-row-conditions
   :universes []
   :type (f/forall [['rows lb] ['w R]] (goal 'rows 'w))
   :value
   (f/lam
    [['rows lb] ['w R]]
    (let [nil-a (nil-of ar)
          nil-b (nil-of br)
          empty-pair (pair la la nil-a nil-a)
          base (witness nil-b 'w empty-pair
                        (both (sat empty-pair 'w) (count-eq empty-pair nil-b)
                              (both (lower-sat nil-a 'w) (upper-sat nil-a 'w)
                                    trivial trivial)
                              (refl nz)))
          step
          (f/lam
           [['head br] ['tail lb] ['ih (goal 'tail 'w)]]
           (f/app
            (f/const* 'proposition/use-witness [tl]) pair-lists
            (pred 'tail 'w) (goal (cons-of br 'head 'tail) 'w) 'ih
            (f/lam
             [['pr pair-lists] ['ev (f/app (pred 'tail 'w) 'pr)]]
             (let [l (first-of 'pr) u (second-of 'pr)
                   rs (cons-of br 'head 'tail)
                   new-l (cons-of ar tautology-row l)
                   new-pr (pair la la new-l u)
                   sat-proof (left (sat 'pr 'w) (count-eq 'pr 'tail) 'ev)
                   length-proof (right (sat 'pr 'w) (count-eq 'pr 'tail) 'ev)
                   new-length-proof
                   (f/app (f/const* 'equality/congruent-function [tl tl]) N N
                          (f/lam [['n N]] (app 'data/succ 'n))
                          (count-sum 'pr) (length-of br 'tail) length-proof)]
               (witness
                rs 'w new-pr
                (both (sat new-pr 'w) (count-eq new-pr rs)
                      (both (lower-sat new-l 'w) (upper-sat u 'w)
                            (both (tautology 'w) (lower-sat l 'w)
                                  (tautology-proof 'w)
                                  (left (lower-sat l 'w) (upper-sat u 'w) sat-proof))
                            (right (lower-sat l 'w) (upper-sat u 'w) sat-proof))
                      new-length-proof))))))]
      (f/app (f/const* 'data/List.rec [tl [:zero]]) br
             (f/lam [['rs lb]] (goal 'rs 'w)) base step 'rows)))})

(def ^:private shipped-type-spec
  {:name 'audit/farkas-covered-type-ignores-reduction
   :universes []
   ;; Read the actual definition-site statement, not an audit copy of its type.
   :type (:type covered/partition-covered-spec)
   :value (f/lam [['rows lb] ['w R]
                  ['reduced (app 'nnrat/farkas-reduced-conditions 'rows 'w)]]
                 (app 'audit/farkas-covering-without-row-conditions 'rows 'w))})

(def ^:private checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      ;; Do not install the covered theorem: neither adversarial proof may use it.
      (-> (:environment checkpoint)
          partition/extend-environment
          (support/extend-with ::provenance-audit [no-premise-spec shipped-type-spec])))))

(defn- elaborate! [env expression]
  (let [r (elaborate/core-expression env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Audit expression did not elaborate" {:result r})))
    (:term r)))

(deftest cardinality-covered-type-admits-a-proof-without-constraints
  (let [env @checked-environment]
    (is (nil? (environment/resolve-id env 'nnrat/farkas-partition-list-covered))
        "The adversarial proof must not depend on the covered theorem")
    (doseq [spec [no-premise-spec shipped-type-spec]]
      (let [id (environment/resolve-id env (:name spec))
            d (environment/declaration env id)]
        (is (some? id))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest kernel-rejects-the-wrong-cardinality-after-successful-elaboration
  (let [env @checked-environment
        nil-a (nil-of ar)
        ;; An arbitrary singleton input requires ONE output row.
        row (pair R covered/bpq z (pair R covered/p2 z (pair R R z z)))
        rows (cons-of br row (nil-of br))
        empty-pair (pair la la nil-a nil-a)
        bad (witness rows z empty-pair
                     (both (sat empty-pair z) (count-eq empty-pair rows)
                           (both (lower-sat nil-a z) (upper-sat nil-a z) trivial trivial)
                           (refl nz)))
        value (elaborate! env bad)
        type (elaborate! env (goal rows z))]
    (is (= :rejected (:status (kernel/check env value type #{})))
        "Failure must be kernel rejection, not an elaboration or setup error")))
