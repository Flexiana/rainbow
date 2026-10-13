(ns rainbow.math.rational.nnrat.farkas-reduce-list
  "Recursive-reduction sub-brick of brick 6 (list form): map the single-row
  reduction over a list of both-sides cross rows.

  The both-sides cross system produced by eliminating a variable is a LIST
  of rows A_i*v + P_i <= B_i*v + Q_i (each row a Product quadruple
  (A,(B,(P,Q)))). nnrat/farkas-reduce-list-necessary proves: if every row
  holds at v (nnrat/farkas-both-sides-rows-satisfied), then every row
  reduces to an affine row in v (nnrat/farkas-reduced-conditions) -- a lower
  row when A_i<=B_i, an upper row when B_i<=A_i -- by applying the single-row
  reduction (nnrat/farkas-both-sides-reduce) to each via List.rec.

  Both predicates still describe rows evaluated at the SAME variable v.
  This theorem converts each both-sides row to a disjunction of affine-row
  conditions; it does not itself eliminate v or produce a related partition
  of output row lists. Eliminating a coordinate requires a separate existential
  projection theorem. The variable-count recursion, partition provenance and
  dual extraction are separate obligations. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-both-sides-reduce :as reduce]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pq (function/app (function/const* 'data/Product [type-level type-level])
                      nnrat nnrat))
(def bpq (function/app (function/const* 'data/Product [type-level type-level])
                       nnrat pq))
(def row (function/app (function/const* 'data/Product [type-level type-level])
                       nnrat bpq))
(def list-row (function/app (function/const* 'data/List [type-level]) row))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equiv [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- bs-a [r] (first-of nnrat bpq r))
(defn- bs-bpq [r] (second-of nnrat bpq r))
(defn- bs-b [r] (first-of nnrat pq (bs-bpq r)))
(defn- bs-pq [r] (second-of nnrat pq (bs-bpq r)))
(defn- bs-p [r] (first-of nnrat nnrat (bs-pq r)))
(defn- bs-q [r] (second-of nnrat nnrat (bs-pq r)))

(defn- conjunction [left right]
  (function/app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- disjunction [left right]
  (function/app (function/const* 'proposition/disjunction []) left right))
(defn- existence [predicate]
  (function/app (function/const* 'proposition/existence [type-level])
                nnrat predicate))
(defn- both-sides-reduce [a b p q v both]
  (function/app (function/const* 'nnrat/farkas-both-sides-reduce [])
                a b p q v both))

;; one row's both-sides condition A*v + P <= B*v + Q, at value v
(defn- row-both-sides [r value]
  (at-most (add (mul (bs-a r) value) (bs-p r))
           (add (mul (bs-b r) value) (bs-q r))))
;; one row's reduced condition (matches farkas-both-sides-reduce's output)
(defn- row-reduced [r value]
  (disjunction
   (existence (function/lam
               [['d nnrat]]
               (conjunction (equiv (add (bs-a r) 'd) (bs-b r))
                            (at-most (bs-p r) (add (mul 'd value) (bs-q r))))))
   (existence (function/lam
               [['d nnrat]]
               (conjunction (equiv (add (bs-b r) 'd) (bs-a r))
                            (at-most (add (mul 'd value) (bs-p r)) (bs-q r)))))))

(defn- rows-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-both-sides-rows-satisfied [])
                rows value))
(defn- reduced-conditions [rows value]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions [])
                rows value))

(def rows-satisfied-spec
  {:name 'nnrat/farkas-both-sides-rows-satisfied
   :kind :definition
   :universes []
   :type (function/arrow list-row nnrat 'Prop)
   :value
   (function/lam
    [['rows list-row] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     row
     (function/lam [['ignored list-row]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head row] ['tail list-row] ['ih 'Prop]]
      (proposition/conjunction (row-both-sides 'head 'value) 'ih))
     'rows))})

(def reduced-conditions-spec
  {:name 'nnrat/farkas-reduced-conditions
   :kind :definition
   :universes []
   :type (function/arrow list-row nnrat 'Prop)
   :value
   (function/lam
    [['rows list-row] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     row
     (function/lam [['ignored list-row]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head row] ['tail list-row] ['ih 'Prop]]
      (proposition/conjunction (row-reduced 'head 'value) 'ih))
     'rows))})

(def definition-specs [rows-satisfied-spec reduced-conditions-spec])

(def reduce-list-necessary-spec
  {:name 'nnrat/farkas-reduce-list-necessary
   :universes []
   :type
   (function/forall
    [['rows list-row] ['v nnrat]
     ['satisfied (rows-satisfied 'rows 'v)]]
    (reduced-conditions 'rows 'v))
   :value
   (function/lam
    [['rows list-row] ['v nnrat]
     ['satisfied (rows-satisfied 'rows 'v)]]
    (let [motive (function/lam
                  [['rs list-row]]
                  (function/arrow (rows-satisfied 'rs 'v)
                                  (reduced-conditions 'rs 'v)))
          nil-case
          (function/lam
           [['hnil (rows-satisfied
                    (function/app (function/const* 'data/nil [type-level]) row)
                    'v)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head row] ['tail list-row]
            ['ih (function/arrow (rows-satisfied 'tail 'v)
                                 (reduced-conditions 'tail 'v))]]
           (function/lam
            [['hcons (rows-satisfied
                      (function/app (function/const* 'data/cons [type-level])
                                    row 'head 'tail)
                      'v)]]
            (let [head-prop (row-both-sides 'head 'v)
                  tail-prop (rows-satisfied 'tail 'v)
                  head-proof (left-conjunct head-prop tail-prop 'hcons)
                  tail-proof (right-conjunct head-prop tail-prop 'hcons)
                  head-reduced
                  (both-sides-reduce (bs-a 'head) (bs-b 'head)
                                     (bs-p 'head) (bs-q 'head) 'v head-proof)]
              (conjoin (row-reduced 'head 'v)
                       (reduced-conditions 'tail 'v)
                       head-reduced
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        row motive nil-case cons-case 'rows)
       'satisfied)))})

(def theorem-specs [reduce-list-necessary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-both-sides-reduce])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-reduce-list (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-reduce-list))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
