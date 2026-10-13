(ns rainbow.math.rational.nnrat.farkas-row-reconstruction
  "Reconstruct a source inequality from its reduced affine row and coefficient
  equation. These are the converse directions to nnrat-farkas-both-sides:

    a+d ~ b, p <= d*v+q  ==>  a*v+p <= b*v+q
    b+d ~ a, d*v+p <= q  ==>  a*v+p <= b*v+q.

  Together with the existing forward theorems they establish row satisfaction
  equivalence at every v. The difference equation is essential provenance;
  cardinality or a sum of constants cannot replace it. Partition completeness
  and the relation between whole input/output lists remain separate obligations.
  Native proof data, no new axioms."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-both-sides :as forward]))

(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b h] (app 'nnrat/equivalent-symmetric a b h))
(defn- trans [a b c ab bc] (app 'nnrat/equivalent-transitive a b c ab bc))

(defn- expanded-affine
  "Given a+d~b, prove b*v+q ~ a*v+(d*v+q)."
  [a d b v q diff]
  (let [bv (mul b v)
        av (mul a v)
        dv (mul d v)
        expanded (add av dv)
        product-eq
        (trans bv (mul (add a d) v) expanded
               (app 'nnrat/multiply-respects-equivalence b (add a d) v v
                    (sym (add a d) b diff) (refl v))
               (app 'nnrat/multiply-distributes-add-right a d v))]
    (trans (add bv q) (add expanded q) (add av (add dv q))
           (app 'nnrat/add-respects-equivalence bv expanded q q product-eq (refl q))
           (app 'nnrat/add-associative av dv q))))

(def lower-to-both-sides-spec
  {:name 'nnrat/farkas-lower-to-both-sides
   :universes []
   :type
   (f/forall [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
              ['diff (eqv (add 'a 'd) 'b)]
              ['reduced (le 'p (add (mul 'd 'v) 'q))]]
             (le (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q)))
   :value
   (f/lam [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
           ['diff (eqv (add 'a 'd) 'b)]
           ['reduced (le 'p (add (mul 'd 'v) 'q))]]
          (let [av (mul 'a 'v)
                lhs (add av 'p)
                remainder (add (mul 'd 'v) 'q)]
            (app 'nnrat/at-most-respects-equivalence
                 lhs lhs (add (mul 'b 'v) 'q) (add av remainder)
                 (refl lhs) (expanded-affine 'a 'd 'b 'v 'q 'diff)
                 (app 'nnrat/add-monotone av av 'p remainder
                      (app 'nnrat/at-most-reflexive av) 'reduced))))})

(def upper-to-both-sides-spec
  {:name 'nnrat/farkas-upper-to-both-sides
   :universes []
   :type
   (f/forall [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
              ['diff (eqv (add 'b 'd) 'a)]
              ['reduced (le (add (mul 'd 'v) 'p) 'q)]]
             (le (add (mul 'a 'v) 'p) (add (mul 'b 'v) 'q)))
   :value
   (f/lam [['a nnrat] ['b nnrat] ['d nnrat] ['p nnrat] ['q nnrat] ['v nnrat]
           ['diff (eqv (add 'b 'd) 'a)]
           ['reduced (le (add (mul 'd 'v) 'p) 'q)]]
          (let [bv (mul 'b 'v)
                rhs (add bv 'q)
                remainder (add (mul 'd 'v) 'p)]
            (app 'nnrat/at-most-respects-equivalence
                 (add (mul 'a 'v) 'p) (add bv remainder) rhs rhs
                 (expanded-affine 'b 'd 'a 'v 'p 'diff) (refl rhs)
                 (app 'nnrat/add-monotone bv bv remainder 'q
                      (app 'nnrat/at-most-reflexive bv) 'reduced))))})

(def definition-specs [])
(def theorem-specs [lower-to-both-sides-spec upper-to-both-sides-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      forward/extend-environment
      (support/extend-with :nnrat-farkas-row-reconstruction theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
