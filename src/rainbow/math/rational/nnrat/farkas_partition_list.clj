(ns rainbow.math.rational.nnrat.farkas-partition-list
  "Piece (ii) brick 1: the dependent
  partition of a reduced disjunction system into a lower-list and an
  upper-list.

  One elimination round's output reduced-conditions is a fold of
  disjunctions. This threads it into the next round: given
  reduced-conditions holds at w, there EXIST a lower-row list and an
  upper-row list -- carried as one Product witness -- such that brick 5b's
  lower fold and brick 4's upper fold both hold at w. The lists' sizes are
  runtime-dependent (each row's lower/upper case is decided per row), so the
  partition is dependent. Proof: List.rec over the reduced rows; the base is
  two empty lists; each cons resolves the head via nnrat/farkas-partition-row
  (lower or upper affine constraint), constructs the corresponding brick
  5b/4 row (a data/pair whose projections reduce to the constraint's fields,
  so the fold predicate is defeq to the constraint), prepends it to the
  matching list, and re-witnesses the Product. nnrat/farkas-partition-list-
  necessary is the whole partition -- the last piece before the layer
  recursion. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-partition-row :as prow]
            [rainbow.math.rational.nnrat.farkas-reduce-list :as reduce-list]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as upper]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list-lower :as lower]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def p2 (product nnrat nnrat))
(def bpq (product nnrat p2))
(def bs-row (product nnrat bpq))                 ; (A,(B,(P,Q))) reduce-list row
(def list-bs (function/app (function/const* 'data/List [type-level]) bs-row))
(def arow (product nnrat p2))                     ; affine row (a,(s,z)) -- 5b & 4 share it
(def list-a (function/app (function/const* 'data/List [type-level]) arow))
(def pair-lists (product list-a list-a))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- pair [a b x y]
  (function/app (function/const* 'data/pair [type-level type-level]) a b x y))
(defn- nil-of [c] (function/app (function/const* 'data/nil [type-level]) c))
(defn- cons-of [c h t] (function/app (function/const* 'data/cons [type-level]) c h t))

;; bs-row field extractors
(defn- bs-a [r] (fst nnrat bpq r))
(defn- bs-b [r] (fst nnrat p2 (snd nnrat bpq r)))
(defn- bs-p [r] (fst nnrat nnrat (snd nnrat p2 (snd nnrat bpq r))))
(defn- bs-q [r] (snd nnrat nnrat (snd nnrat p2 (snd nnrat bpq r))))

(defn- reduced-conditions [rows w]
  (function/app (function/const* 'nnrat/farkas-reduced-conditions []) rows w))
(defn- row-reduced [r w]
  ;; reduce-list's per-row disjunction, in partition-row's shape
  (proposition/disjunction
   (function/app (function/const* 'proposition/existence [type-level]) nnrat
                 (function/lam [['d nnrat]]
                               (proposition/conjunction
                                (equiv (add (bs-a r) 'd) (bs-b r))
                                (at-most (bs-p r) (add (mul 'd w) (bs-q r))))))
   (function/app (function/const* 'proposition/existence [type-level]) nnrat
                 (function/lam [['d nnrat]]
                               (proposition/conjunction
                                (equiv (add (bs-b r) 'd) (bs-a r))
                                (at-most (add (mul 'd w) (bs-p r)) (bs-q r)))))))
(defn- lowers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied [])
                rows w))
(defn- uppers-sat [rows w]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows w))
(defn- partition-row [a b p q w reduced]
  (function/app (function/const* 'nnrat/farkas-partition-row [])
                a b p q w reduced))

(defn- conjunction [l r] (function/app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- disjunction [l r] (function/app (function/const* 'proposition/disjunction []) l r))
(defn- use-disjunction [l r result e onl onr]
  (function/app (function/const* 'proposition/use-disjunction []) l r result e onl onr))
(defn- existence [pred]
  (function/app (function/const* 'proposition/existence [type-level]) pair-lists pred))
(defn- witness [pred value evidence]
  (function/app (function/const* 'proposition/witness [type-level]) pair-lists pred value evidence))
(defn- use-witness [pred result evidence cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) pair-lists pred result evidence cont))
(defn- existence-nn [pred]
  (function/app (function/const* 'proposition/existence [type-level]) nnrat pred))
(defn- use-witness-nn [pred result evidence cont]
  (function/app (function/const* 'proposition/use-witness [type-level]) nnrat pred result evidence cont))

;; the goal predicate: for a Product of (lowers, uppers), both folds hold at w
(defn- goal-pred [w]
  (function/lam
   [['pr pair-lists]]
   (conjunction (lowers-sat (fst list-a list-a 'pr) w)
                (uppers-sat (snd list-a list-a 'pr) w))))
(defn- goal [w] (existence (goal-pred w)))

;; constructed affine rows from a partition witness d and the bs fields
(defn- lower-row [d q p] (pair nnrat p2 d (pair nnrat nnrat q p)))  ; (d,(q,p))
(defn- upper-row [d p q] (pair nnrat p2 d (pair nnrat nnrat p q)))  ; (d,(p,q))
;; the affine constraints (defeq to the fold predicates of the rows above)
(defn- lower-holds [p d w q] (at-most p (add (mul d w) q)))
(defn- upper-holds [d w p q] (at-most (add (mul d w) p) q))

(def partition-list-spec
  {:name 'nnrat/farkas-partition-list-necessary
   :universes []
   :type
   (function/forall
    [['rows list-bs] ['w nnrat]
     ['reduced (reduced-conditions 'rows 'w)]]
    (goal 'w))
   :value
   (function/lam
    [['rows list-bs] ['w nnrat]
     ['reduced (reduced-conditions 'rows 'w)]]
    (let [motive (function/lam
                  [['rs list-bs]]
                  (function/arrow (reduced-conditions 'rs 'w) (goal 'w)))
          nil-case
          (function/lam
           [['hnil (reduced-conditions (nil-of bs-row) 'w)]]
           (witness (goal-pred 'w) (pair list-a list-a (nil-of arow) (nil-of arow))
                    (conjoin (lowers-sat (nil-of arow) 'w) (uppers-sat (nil-of arow) 'w)
                             (function/const* 'proposition/trivial [])
                             (function/const* 'proposition/trivial []))))
          cons-case
          (function/lam
           [['head bs-row] ['tail list-bs]
            ['ih (function/arrow (reduced-conditions 'tail 'w) (goal 'w))]]
           (function/lam
            [['hcons (reduced-conditions (cons-of bs-row 'head 'tail) 'w)]]
            (let [rr (row-reduced 'head 'w)
                  rest (reduced-conditions 'tail 'w)
                  r-red (left-conjunct rr rest 'hcons)
                  tail-red (right-conjunct rr rest 'hcons)
                  ih-goal (function/app 'ih tail-red)
                  ;; the two stripped-constraint existences from partition-row
                  lo-out (existence-nn (function/lam [['d nnrat]]
                                                     (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))))
                  up-out (existence-nn (function/lam [['d nnrat]]
                                                     (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))))
                  part (partition-row (bs-a 'head) (bs-b 'head) (bs-p 'head) (bs-q 'head) 'w r-red)]
              ;; consume the ih witness (lowers L0, uppers U0), then partition head
              (use-witness
               (goal-pred 'w) (goal 'w) ih-goal
               (function/lam
                [['pr pair-lists]
                 ['pr-proof (function/app (goal-pred 'w) 'pr)]]
                (let [l0 (fst list-a list-a 'pr)
                      u0 (snd list-a list-a 'pr)
                      lo-sat0 (left-conjunct (lowers-sat l0 'w) (uppers-sat u0 'w) 'pr-proof)
                      up-sat0 (right-conjunct (lowers-sat l0 'w) (uppers-sat u0 'w) 'pr-proof)]
                  (use-disjunction
                   lo-out up-out (goal 'w) part
                   ;; head is a lower constraint
                   (function/lam
                    [['lo lo-out]]
                    (use-witness-nn
                     (function/lam [['d nnrat]]
                                   (lower-holds (bs-p 'head) 'd 'w (bs-q 'head)))
                     (goal 'w) 'lo
                     (function/lam
                      [['d nnrat]
                       ['dh (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))]]
                      (let [new-l (cons-of arow (lower-row 'd (bs-q 'head) (bs-p 'head)) l0)]
                        (witness (goal-pred 'w) (pair list-a list-a new-l u0)
                                 (conjoin (lowers-sat new-l 'w) (uppers-sat u0 'w)
                                          (conjoin (lower-holds (bs-p 'head) 'd 'w (bs-q 'head))
                                                   (lowers-sat l0 'w) 'dh lo-sat0)
                                          up-sat0))))))
                   ;; head is an upper constraint
                   (function/lam
                    [['up up-out]]
                    (use-witness-nn
                     (function/lam [['d nnrat]]
                                   (upper-holds 'd 'w (bs-p 'head) (bs-q 'head)))
                     (goal 'w) 'up
                     (function/lam
                      [['d nnrat]
                       ['dh (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))]]
                      (let [new-u (cons-of arow (upper-row 'd (bs-p 'head) (bs-q 'head)) u0)]
                        (witness (goal-pred 'w) (pair list-a list-a l0 new-u)
                                 (conjoin (lowers-sat l0 'w) (uppers-sat new-u 'w)
                                          lo-sat0
                                          (conjoin (upper-holds 'd 'w (bs-p 'head) (bs-q 'head))
                                                   (uppers-sat u0 'w) 'dh up-sat0))))))))))))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        bs-row motive nil-case cons-case 'rows)
       'reduced)))})

(def definition-specs [])
(def theorem-specs [partition-list-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      prow/extend-environment
      reduce-list/extend-environment
      upper/extend-environment
      lower/extend-environment
      (support/extend-with :nnrat-farkas-partition-list
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
