(ns rainbow.math.rational.nnrat.farkas-both-sides-reduce
  "Recursive-reduction sub-brick of brick 6 (single-row core): reduce a
  both-sides cross row to an affine row in the surviving variable.

  Eliminating a variable v across the general Fourier-Motzkin step, each
  bilist cross condition is a both-sides row A*v + P <= B*v + Q (brick 6
  cross-product core). This reduces it, subtraction-free, to an affine row
  in v: nnrat/farkas-both-sides-reduce proves

    (A*v+P <= B*v+Q)  ->  (EXISTS D, A+D~B /\\ P <= D*v+Q)
                          OR (EXISTS D, B+D~A /\\ D*v+P <= Q)

  -- a LOWER affine row when A<=B, an UPPER affine row when B<=A. The
  case-split uses nnrat/at-most-total (the order is total), the difference
  witness comes from nnrat/at-most-difference, and the conversions are
  nnrat/farkas-both-sides-to-lower and -to-upper. So the both-sides cross
  system becomes a mixed affine-row system in one fewer variable, which
  bricks 4/5b eliminate. Mapping this over the bilist cross-condition list
  (and threading it through the variable-count induction) is the remaining
  n-variable capstone. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.order-total :as total]
            [rainbow.math.rational.nnrat.farkas-both-sides :as both-sides]
            [rainbow.math.rational.nnrat.order-difference :as difference]))

(def type-level [:succ [:zero]])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equiv [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- conjunction [left right]
  (function/app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- disjunction [left right]
  (function/app (function/const* 'proposition/disjunction []) left right))
(defn- left-disjunct [left right evidence]
  (function/app (function/const* 'proposition/left-disjunct []) left right evidence))
(defn- right-disjunct [left right evidence]
  (function/app (function/const* 'proposition/right-disjunct []) left right evidence))
(defn- use-disjunction [left right result evidence on-left on-right]
  (function/app (function/const* 'proposition/use-disjunction [])
                left right result evidence on-left on-right))
(defn- existence [predicate]
  (function/app (function/const* 'proposition/existence [type-level])
                nnrat predicate))
(defn- witness [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat predicate value evidence))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nnrat predicate result evidence continue))
(defn- at-most-total [a b]
  (function/app (function/const* 'nnrat/at-most-total []) a b))
(defn- at-most-difference [x y ordered]
  (function/app (function/const* 'nnrat/at-most-difference []) x y ordered))
(defn- to-lower [a b d p q v diff both]
  (function/app (function/const* 'nnrat/farkas-both-sides-to-lower [])
                a b d p q v diff both))
(defn- to-upper [a b d p q v diff both]
  (function/app (function/const* 'nnrat/farkas-both-sides-to-upper [])
                a b d p q v diff both))

(def both-sides-reduce-spec
  {:name 'nnrat/farkas-both-sides-reduce
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['both (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (disjunction
     (existence (function/lam
                 [['d nnrat]]
                 (conjunction (equiv (add 'a 'd) 'b)
                              (at-most 'p (add (mul 'd 'v) 'q)))))
     (existence (function/lam
                 [['d nnrat]]
                 (conjunction (equiv (add 'b 'd) 'a)
                              (at-most (add (mul 'd 'v) 'p) 'q))))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
     ['both (at-most (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q))]]
    (let [lower-pred (function/lam
                      [['d nnrat]]
                      (conjunction (equiv (add 'a 'd) 'b)
                                   (at-most 'p (add (mul 'd 'v) 'q))))
          upper-pred (function/lam
                      [['d nnrat]]
                      (conjunction (equiv (add 'b 'd) 'a)
                                   (at-most (add (mul 'd 'v) 'p) 'q)))
          lower-exists (existence lower-pred)
          upper-exists (existence upper-pred)
          result (disjunction lower-exists upper-exists)
          diff-pred-ab (function/lam [['w nnrat]] (equiv (add 'a 'w) 'b))
          diff-pred-ba (function/lam [['w nnrat]] (equiv (add 'b 'w) 'a))]
      (use-disjunction
       (at-most 'a 'b) (at-most 'b 'a) result (at-most-total 'a 'b)
       ;; A <= B : affine lower row
       (function/lam
        [['a-le-b (at-most 'a 'b)]]
        (use-witness
         diff-pred-ab result (at-most-difference 'a 'b 'a-le-b)
         (function/lam
          [['d nnrat] ['hd (equiv (add 'a 'd) 'b)]]
          (left-disjunct
           lower-exists upper-exists
           (witness lower-pred 'd
                    (conjoin (equiv (add 'a 'd) 'b)
                             (at-most 'p (add (mul 'd 'v) 'q))
                             'hd
                             (to-lower 'a 'b 'd 'p 'q 'v 'hd 'both)))))))
       ;; B <= A : affine upper row
       (function/lam
        [['b-le-a (at-most 'b 'a)]]
        (use-witness
         diff-pred-ba result (at-most-difference 'b 'a 'b-le-a)
         (function/lam
          [['d nnrat] ['hd (equiv (add 'b 'd) 'a)]]
          (right-disjunct
           lower-exists upper-exists
           (witness upper-pred 'd
                    (conjoin (equiv (add 'b 'd) 'a)
                             (at-most (add (mul 'd 'v) 'p) 'q)
                             'hd
                             (to-upper 'a 'b 'd 'p 'q 'v 'hd 'both))))))))))})

(def definition-specs [])
(def theorem-specs [both-sides-reduce-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.farkas-both-sides rainbow.math.rational.nnrat.order-difference])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-both-sides-reduce (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-both-sides-reduce))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
