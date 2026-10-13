(ns rainbow.math.sums.value-append
  "Split the existing expr-sum-value at any Nat offset a:
   sum F (b+a) ~ sum F a + sum (fn i. F(i+a)) b.
   All Nat lengths, including zero; no sign or boundedness assumptions.
   Equality is the existing signed-rational equivalence, not raw-pair Eq."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s
             :refer [nat zero family call at sum add eqv refl sym trans]]
            [rainbow.math.rational.signed.add-associative :as associative]))

(defn nadd [x y] (call 'algebra/nat-add x y))

(def append-spec
  (let [shift (f/lam [['i nat]] (at 'F (nadd 'i 'a)))
        claim #(eqv (sum 'F (nadd % 'a)) (add (sum 'F 'a) (sum shift %)))]
    (s/spec 'signed/expr-sum-value-append [['F family] ['a nat] ['b nat]] (claim 'b)
            (s/induct claim (sym (add (sum 'F 'a) zero) (sum 'F 'a) (call 'signed/add-zero-right (sum 'F 'a)))
                      (fn [q ih]
                        (let [x (sum 'F (nadd q 'a)) a (sum 'F 'a) b (sum shift q) c (at 'F (nadd q 'a))]
                          (trans (add x c) (add (add a b) c) (add a (add b c))
                                 (s/add-cong x (add a b) c c ih (refl c))
                                 (call 'signed/add-associative a b c)))) 'b))))

(def theorem-specs [append-spec])
(defn extend-environment [env]
  (-> env s/extend-environment associative/extend-environment
      (support/extend-with :expr-sum-value-append theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
