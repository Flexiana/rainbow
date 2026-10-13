(ns rainbow.math.rational.nnrat.farkas-reduced-list-satisfied
  "Farkas elimination REDUCTION CORRECTNESS (the SUFFICIENCY direction):

    nnrat/farkas-reduced-list-satisfied :
      forall rows w, farkas-reduced-conditions rows w
                   -> farkas-both-sides-rows-satisfied rows w

  The existing forward theorem (reduce-list-necessary) proves satisfaction =>
  reduced (reduced conditions are NECESSARY). This proves the converse: the
  reduced conditions are SUFFICIENT for the original both-sides system to be
  satisfied at w. Together they give the equivalence that makes the reduced
  system a faithful stand-in for the source.

  SCOPE (kept honest): this is REDUCTION CORRECTNESS, NOT partition
  provenance. Its conclusion is about the SOURCE rows (row-both-sides per row);
  there is no existential output partition here, so it is non-vacuous by
  construction -- a tautology-fill has nothing to attach to, and proving
  row-both-sides for every row REQUIRES the per-row reduced disjunction (the
  premise), so a premise-ignoring proof is impossible (negative control:
  the source singleton (0,0,1,0) is unsatisfiable). It does NOT relate the
  ∃(l,u) partition covering to the input rows; that partition-provenance question
  remains separate and open. Adding this as a conjunct to ∃(l,u),sat would still
  admit tautology outputs on a feasible source -- so it is reported on its own,
  not as the covering fix.

  Proof: List.rec on rows. nil -> truth. cons head tail -> split the premise into
  (row-reduced head w) and (reduced-conditions tail w); the IH on the tail gives
  (both-sides-satisfied tail w); use-disjunction on (row-reduced head w) feeds
  reverse lemmas -- farkas-lower-to-both-sides (from a+d~b and
  p<=d*w+q) and farkas-upper-to-both-sides (from b+d~a and d*w+p<=q) -- to
  reconstruct (row-both-sides head w); conjoin. Direction-neutral (a standalone
  theorem; does not rewire the covered chain or the Feasible predicate). Native
  proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-row-reconstruction :as recon]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pq (product nnrat nnrat))
(def bpq (product nnrat pq))
(def row (product nnrat bpq))
(def list-row (function/app (function/const* 'data/List [type-level]) row))

(defn- add [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- mul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- fo [l r v] (function/app (function/const* 'product/first [type-level type-level]) l r v))
(defn- so [l r v] (function/app (function/const* 'product/second [type-level type-level]) l r v))
(defn- bs-a [r] (fo nnrat bpq r))
(defn- bs-b [r] (fo nnrat pq (so nnrat bpq r)))
(defn- bs-p [r] (fo nnrat nnrat (so nnrat pq (so nnrat bpq r))))
(defn- bs-q [r] (so nnrat nnrat (so nnrat pq (so nnrat bpq r))))

(defn- conjunction [a b] (function/app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b p q] (function/app (function/const* 'proposition/conjoin []) a b p q))
(defn- left-conjunct [a b h] (function/app (function/const* 'proposition/left []) a b h))
(defn- right-conjunct [a b h] (function/app (function/const* 'proposition/right []) a b h))
(defn- disjunction [a b] (function/app (function/const* 'proposition/disjunction []) a b))
(defn- existence [pred] (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- use-disjunction [l r result e onl onr]
  (function/app (function/const* 'proposition/use-disjunction []) l r result e onl onr))
(defn- use-witness [pred result e cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) nnrat pred result e cont))
(def trivial (function/const* 'proposition/trivial []))

(defn- reduced-conditions [rows w]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows w))
(defn- both-sides-satisfied [rows w]
  (function/app (function/const* 'nnrat/farkas-both-sides-rows-satisfied []) rows w))
;; one row's both-sides condition A*w + P <= B*w + Q (matches reduce_list/row-both-sides)
(defn- row-both-sides [r w]
  (at-most (add (mul (bs-a r) w) (bs-p r)) (add (mul (bs-b r) w) (bs-q r))))
;; the two disjuncts of row-reduced
(defn- lower-pred [r w]
  (function/lam [['d nnrat]]
                (conjunction (equiv (add (bs-a r) 'd) (bs-b r))
                             (at-most (bs-p r) (add (mul 'd w) (bs-q r))))))
(defn- upper-pred [r w]
  (function/lam [['d nnrat]]
                (conjunction (equiv (add (bs-b r) 'd) (bs-a r))
                             (at-most (add (mul 'd w) (bs-p r)) (bs-q r)))))
(defn- lower-ex [r w] (existence (lower-pred r w)))
(defn- upper-ex [r w] (existence (upper-pred r w)))
(defn- row-reduced [r w] (disjunction (lower-ex r w) (upper-ex r w)))

(defn- nil-row [] (function/app (function/const* 'data/nil [type-level]) row))
(defn- cons-row [h t] (function/app (function/const* 'data/cons [type-level]) row h t))
(defn- lower-to-both-sides [a b d p q w diff red]
  (function/app (function/const* 'nnrat/farkas-lower-to-both-sides []) a b d p q w diff red))
(defn- upper-to-both-sides [a b d p q w diff red]
  (function/app (function/const* 'nnrat/farkas-upper-to-both-sides []) a b d p q w diff red))

(def reduced-list-satisfied-spec
  {:name 'nnrat/farkas-reduced-list-satisfied
   :universes []
   :type
   (function/forall [['rows list-row] ['w nnrat]]
                    (function/arrow (reduced-conditions 'rows 'w) (both-sides-satisfied 'rows 'w)))
   :value
   (function/lam
    [['rows list-row] ['w nnrat]]
    (let [motive (function/lam [['rs list-row]]
                               (function/arrow (reduced-conditions 'rs 'w) (both-sides-satisfied 'rs 'w)))
          nil-case (function/lam [['h (reduced-conditions (nil-row) 'w)]] trivial)
          cons-case
          (function/lam
           [['head row] ['tail list-row]
            ['ih (function/arrow (reduced-conditions 'tail 'w) (both-sides-satisfied 'tail 'w))]]
           (function/lam
            [['hc (reduced-conditions (cons-row 'head 'tail) 'w)]]
            (let [rr (row-reduced 'head 'w)
                  rt (reduced-conditions 'tail 'w)
                  r-red (left-conjunct rr rt 'hc)
                  tail-red (right-conjunct rr rt 'hc)
                  bs-tail (function/app 'ih tail-red)
                  lp (lower-pred 'head 'w)
                  up (upper-pred 'head 'w)
                  lower-branch
                  (function/lam
                   [['lo (lower-ex 'head 'w)]]
                   (use-witness lp (row-both-sides 'head 'w) 'lo
                                (function/lam
                                 [['d nnrat] ['dh (function/app lp 'd)]]
                                 (let [le (equiv (add (bs-a 'head) 'd) (bs-b 'head))
                                       lr (at-most (bs-p 'head) (add (mul 'd 'w) (bs-q 'head)))]
                                   (lower-to-both-sides (bs-a 'head) (bs-b 'head) 'd (bs-p 'head) (bs-q 'head) 'w
                                                        (left-conjunct le lr 'dh)
                                                        (right-conjunct le lr 'dh))))))
                  upper-branch
                  (function/lam
                   [['up-ev (upper-ex 'head 'w)]]
                   (use-witness up (row-both-sides 'head 'w) 'up-ev
                                (function/lam
                                 [['d nnrat] ['dh (function/app up 'd)]]
                                 (let [ue (equiv (add (bs-b 'head) 'd) (bs-a 'head))
                                       ur (at-most (add (mul 'd 'w) (bs-p 'head)) (bs-q 'head))]
                                   (upper-to-both-sides (bs-a 'head) (bs-b 'head) 'd (bs-p 'head) (bs-q 'head) 'w
                                                        (left-conjunct ue ur 'dh)
                                                        (right-conjunct ue ur 'dh))))))
                  bs-head (use-disjunction (lower-ex 'head 'w) (upper-ex 'head 'w) (row-both-sides 'head 'w)
                                           r-red lower-branch upper-branch)]
              (conjoin (row-both-sides 'head 'w) (both-sides-satisfied 'tail 'w) bs-head bs-tail))))]
      (function/app (function/const* 'data/List.rec [type-level zero-level])
                    row motive nil-case cons-case 'rows)))})

(def definition-specs [])
(def theorem-specs [reduced-list-satisfied-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      recon/extend-environment
      reduce-list/extend-environment
      (support/extend-with :nnrat-farkas-reduced-list-satisfied
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
