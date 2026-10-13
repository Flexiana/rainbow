(ns rainbow.math.nat.distributive
  "Left-distributivity of nat multiplication over addition:

      a * (b + c) = a * b + a * c   for all a, b, c,

  the semiring law missing from nat_semiring (which has associativity,
  commutativity of addition, multiply-one-right, but not distributivity). Proved
  axiom-free by induction on the FIRST factor a (nat/multiply recurses on its
  left argument). The base a = 0 is reflexive (both sides reduce to 0). The
  successor step reduces the goal, via the multiply computation rule, to a
  commutative-monoid rearrangement

      (b + c) + (p*b + p*c) = (b + p*b) + (c + p*c),

  which is discharged by routing both sides through the common term
  b + ((c + p*b) + p*c) using add associativity (algebra/nat-add-associative) and
  add commutativity (nat/add-commutative), transported with equality/transitive,
  equality/symmetric, and equality/congruent-function.

  This unblocks the geometric-convergence denominator closed form
  den(seq d0 N) = den(d0) * 2^N, the last analytic ingredient of the general
  forall-epsilon convergence modulus, and fills a fundamental gap in the nat
  semiring."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- mul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- add [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq [x y] (function/equality type-level nat x y))
(defn- trans [x y z h1 h2]
  (function/app (function/const* 'equality/transitive [type-level])
                nat x y z h1 h2))
(defn- sym [x y h]
  (function/app (function/const* 'equality/symmetric [type-level]) nat x y h))
(defn- cong [f x y h]
  (function/app (function/const* 'equality/congruent-function
                                 [type-level type-level])
                nat nat f x y h))
(defn- refl [x]
  (function/app (function/const* 'equality/reflexive [type-level]) nat x))
(defn- assoc [a b c]
  (function/app (function/const* 'nat/add-associative []) a b c))
(defn- comm [a b]
  (function/app (function/const* 'nat/add-commutative []) a b))

;; a * (b + c) = a * b + a * c
(def distributive-spec
  {:name 'nat/multiply-distributes-add :universes []
   :type (function/forall
          [['a nat] ['b nat] ['c nat]]
          (eq (mul 'a (add 'b 'c)) (add (mul 'a 'b) (mul 'a 'c))))
   :value
   (function/lam
    [['a nat] ['b nat] ['c nat]]
    (let [motive (function/lam
                  [['m nat]]
                  (function/forall
                   [['x nat] ['y nat]]
                   (eq (mul 'm (add 'x 'y)) (add (mul 'm 'x) (mul 'm 'y)))))
          base (function/lam
                [['x nat] ['y nat]]
                (refl (mul (function/const* 'data/zero []) (add 'x 'y))))
          step
          (function/lam
           [['p nat] ['ih (function/app motive 'p)]]
           (function/lam
            [['x nat] ['y nat]]
            (let [pb (mul 'p 'x)
                  pc (mul 'p 'y)
                  bc (add 'x 'y)
                  ;; step1 : (succ p)*(x+y) = (x+y) + (p*x + p*y)
                  step1 (cong (function/lam [['v nat]] (add bc 'v))
                              (mul 'p bc) (add pb pc)
                              (function/app 'ih 'x 'y))
                  ;; meeting point M = x + ((y + p*x) + p*y)
                  meet (add 'x (add (add 'y pb) pc))
                  ;; LHS -> M
                  la1 (assoc 'x 'y (add pb pc))          ; (x+y)+(pb+pc)=x+(y+(pb+pc))
                  la2 (cong (function/lam [['v nat]] (add 'x 'v))
                            (add 'y (add pb pc)) (add (add 'y pb) pc)
                            (sym (add (add 'y pb) pc) (add 'y (add pb pc))
                                 (assoc 'y pb pc)))
                  lhs->m (trans (add bc (add pb pc))
                                (add 'x (add 'y (add pb pc)))
                                meet la1 la2)
                  ;; M -> RHS = (x + p*x) + (y + p*y)
                  ra1 (cong (function/lam [['v nat]] (add 'x (add 'v pc)))
                            (add 'y pb) (add pb 'y) (comm 'y pb))
                  ra2 (cong (function/lam [['v nat]] (add 'x 'v))
                            (add (add pb 'y) pc) (add pb (add 'y pc))
                            (assoc pb 'y pc))
                  ra3 (sym (add (add 'x pb) (add 'y pc))
                           (add 'x (add pb (add 'y pc)))
                           (assoc 'x pb (add 'y pc)))
                  m->rhs (trans meet
                                (add 'x (add pb (add 'y pc)))
                                (add (add 'x pb) (add 'y pc))
                                (trans meet
                                       (add 'x (add (add pb 'y) pc))
                                       (add 'x (add pb (add 'y pc)))
                                       ra1 ra2)
                                ra3)
                  ;; step2 : (x+y)+(pb+pc) = (x+p*x) + (y+p*y)
                  step2 (trans (add bc (add pb pc)) meet
                               (add (add 'x pb) (add 'y pc))
                               lhs->m m->rhs)]
              (trans (mul (succ 'p) bc)
                     (add bc (add pb pc))
                     (add (mul (succ 'p) 'x) (mul (succ 'p) 'y))
                     step1 step2))))]
      (function/app
       (function/app
        (function/const* 'data/Nat.rec [zero-level])
        motive base step 'a)
       'b 'c)))})

;; x * 0 = 0 for every x -- the other missing semiring law (nat/multiply
;; recurses on its left argument, so x*0 is stuck for abstract x and needs the
;; theorem). By induction on x: base 0*0 = 0 is reflexive; the successor step is
;; the induction hypothesis itself, since (succ p)*0 reduces to 0 + (p*0) = p*0.
(def multiply-zero-right-spec
  {:name 'nat/multiply-zero-right :universes []
   :type (function/forall [['x nat]]
                          (eq (mul 'x (function/const* 'data/zero []))
                              (function/const* 'data/zero [])))
   :value
   (function/lam
    [['x nat]]
    (let [zero-t (function/const* 'data/zero [])
          motive (function/lam [['m nat]] (eq (mul 'm zero-t) zero-t))
          base (refl zero-t)
          step (function/lam [['p nat] ['ih (function/app motive 'p)]] 'ih)]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive base step 'x)))})

(def definition-specs [])
(def theorem-specs [distributive-spec multiply-zero-right-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nat-distributive theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
