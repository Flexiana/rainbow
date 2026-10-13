(ns rainbow.data.binary-test
  "The data/Bin foundation stone: the block installs and its recursor reduces.

  Runs from a cold JVM (lein test), so it is reproducible from a clean environment.
  Verifies (1) the inductive block is accepted and Bin / its constructors /
  Bin.rec resolve, and (2) Bin.rec actually REDUCES: a fold that maps each
  non-zero constructor to `succ` computes the constructor count of a concrete Bin,
  checked by reflexivity. The recursor's motive-elimination level is
  [:succ [:zero]] (the same one Nat.rec uses).

  This is the type + working recursor only; the Bin<->Nat interpretation and
  arithmetic are the next bricks (see the module docstring)."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.data.binary :as binary]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]))

(def ^:private tl [:succ [:zero]])

(def ^:private env
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (binary/extend-environment (:environment checkpoint)))))

(defn- c [nm & a] (apply f/app (f/const* nm []) a))
(def ^:private nat (f/const* 'data/Nat []))
(def ^:private z (f/const* 'data/zero []))
(defn- succ [n] (c 'data/succ n))
(defn- numeral [k] (nth (iterate succ z) k))
(def ^:private Bin (f/const* 'data/Bin []))
(def ^:private bz (f/const* 'data/bin-zero []))
(defn- be [x] (c 'data/bin-even x))
(defn- bo [x] (c 'data/bin-odd x))

;; count the non-zero constructors of a Bin, folding through Bin.rec into Nat.
(defn- constructor-count [b]
  (f/app (f/const* 'data/Bin.rec [tl])
         (f/lam [['x Bin]] nat)
         z
         (f/lam [['h Bin] ['ih nat]] (succ 'ih))
         (f/lam [['h Bin] ['ih nat]] (succ 'ih))
         b))

(defn- checks? [e value type]
  (let [ve (elaborate/core-expression e value)
        te (elaborate/core-expression e type)]
    (and (= :elaborated (:status ve)) (= :elaborated (:status te))
         (= :checked (:status (kernel/check e (:term ve) (:term te) #{}))))))

(deftest bin-block-installs
  (testing "data/Bin, its constructors, data/Bin.rec, and bin/to-nat resolve after install"
    (let [e @env]
      (doseq [alias '[data/Bin data/bin-zero data/bin-even data/bin-odd data/Bin.rec
                      bin/double bin/to-nat bin/bin-succ bin/from-nat bin/bin-add
                      bin/bit-length bin/to-nat-of-bin-succ bin/to-nat-from-nat
                      bin/double-distributes-add bin/to-nat-bin-add
                      bin/double-self bin/double-multiply-left bin/bin-multiply
                      bin/to-nat-bin-multiply bin/nonzero bin/compare bin/at-most
                      bin/compare-reflects bin/at-most-reflects]]
        (is (some? (environment/resolve-id e alias)) (str alias))))))

(defn- checked-and-axiom-free? [e alias]
  (let [id (environment/resolve-id e alias)
        d (environment/declaration e id)]
    (and id
         (= :checked (:status (kernel/check e (:rainbow/value d) (:rainbow/type d)
                                            (set (:rainbow/universes d)))))
         (= #{} (kernel/axioms e id)))))

(deftest bin-nat-faithfulness-is-proved
  (testing "the Nat -> Bin -> Nat round trip is the identity, proved by induction,
            axiom-free: bin/to-nat-from-nat (to-nat (from-nat n) = n) and its
            support lemma bin/to-nat-of-bin-succ (to-nat (bin-succ b) = succ (to-nat b))"
    (let [e @env]
      (is (checked-and-axiom-free? e 'bin/to-nat-of-bin-succ) "support lemma")
      (is (checked-and-axiom-free? e 'bin/to-nat-from-nat) "faithfulness")
      ;; the supporting definitions are checked + axiom-free too
      (is (checked-and-axiom-free? e 'bin/bin-succ))
      (is (checked-and-axiom-free? e 'bin/from-nat))
      (is (checked-and-axiom-free? e 'bin/double)))))

(deftest bin-add-is-checked-and-correct
  (testing "bin/bin-add (O(log) binary addition, carry via bin-succ) is checked and
            axiom-free, and computes the right sum: to-nat (bin-add (from-nat a)
            (from-nat b)) = a + b on concrete pairs (general correctness theorem is
            the next brick)"
    (let [e @env]
      (is (checked-and-axiom-free? e 'bin/bin-add))
      ;; the GENERAL correctness theorem, proved by double induction
      (is (checked-and-axiom-free? e 'bin/double-distributes-add) "double distributes over nat-add")
      (is (checked-and-axiom-free? e 'bin/to-nat-bin-add)
          "to-nat (bin-add a b) = nat-add (to-nat a) (to-nat b), forall a b")
      (let [add (fn [a b] (c 'bin/bin-add a b))
            to-nat (fn [b] (c 'bin/to-nat b))
            from (fn [k] (c 'bin/from-nat (numeral k)))
            eqk (fn [a b] (f/equality tl nat (to-nat (add (from a) (from b))) (numeral (+ a b))))
            refl (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))]
        (doseq [[a b] [[0 0] [1 0] [0 1] [1 1] [2 3] [5 3] [6 7]]]
          (is (checks? e (refl (+ a b)) (eqk a b)) (str a " + " b)))))))

(deftest bin-multiply-is-checked-and-correct
  (testing "bin/bin-multiply (O(log) binary multiplication) is checked + axiom-free
            and computes the right product; its supporting nat lemmas double-self
            (double y = y+y) and double-multiply-left (double(x*y) = (double x)*y)
            are proved theorems, as is the GENERAL correctness theorem
            to-nat(bin-multiply a b) = nat-multiply (to-nat a)(to-nat b), forall a b."
    (let [e @env]
      (is (checked-and-axiom-free? e 'bin/double-self) "double y = y + y")
      (is (checked-and-axiom-free? e 'bin/double-multiply-left) "double(x*y) = (double x)*y")
      (is (checked-and-axiom-free? e 'bin/bin-multiply))
      (is (checked-and-axiom-free? e 'bin/to-nat-bin-multiply)
          "to-nat (bin-multiply a b) = nat-multiply (to-nat a) (to-nat b), forall a b")
      (let [mul (fn [a b] (c 'bin/bin-multiply a b))
            to-nat (fn [b] (c 'bin/to-nat b))
            from (fn [k] (c 'bin/from-nat (numeral k)))
            eqk (fn [a b] (f/equality tl nat (to-nat (mul (from a) (from b))) (numeral (* a b))))
            refl (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))]
        (doseq [[a b] [[0 5] [1 3] [3 4] [6 7]]]
          (is (checks? e (refl (* a b)) (eqk a b)) (str a " * " b)))))))

(deftest bin-at-most-is-checked-and-correct
  (testing "bin/at-most (O(log) LSB-first comparison, carrying le+lt as a
            Product Bool Bool via bin/compare to handle the strict odd/even case) is
            checked + axiom-free and computes the right Bool: at-most (from a)(from b)
            = (a <= b) on concrete pairs, including the odd/even boundaries. The
            GENERAL correctness theorem bin/at-most-reflects (agreement with the unary
            decider nat/decide-at-most through to-nat, forall a b) is proved too."
    (let [e @env
          bool (f/const* 'data/Bool [])
          from (fn [k] (c 'bin/from-nat (numeral k)))
          at-most (fn [a b] (c 'bin/at-most (from a) (from b)))
          bval (fn [t] (if t (f/const* 'data/true []) (f/const* 'data/false [])))
          eqk (fn [a b] (f/equality tl bool (at-most a b) (bval (<= a b))))
          refl (fn [a b] (f/app (f/const* 'equality/reflexive [tl]) bool (bval (<= a b))))]
      (is (checked-and-axiom-free? e 'bin/nonzero))
      (is (checked-and-axiom-free? e 'bin/compare))
      (is (checked-and-axiom-free? e 'bin/at-most))
      (is (checked-and-axiom-free? e 'bin/compare-reflects)
          "strengthened invariant: (le,lt) reflect nat/decide-at-most, forall a b")
      (is (checked-and-axiom-free? e 'bin/at-most-reflects)
          "bin/at-most a b = nat/decide-at-most (to-nat a) (to-nat b), forall a b")
      (doseq [[a b] [[0 0] [0 3] [3 0] [2 2] [3 5] [5 3] [6 7] [7 6] [4 4] [1 8]]]
        (is (checks? e (refl a b) (eqk a b)) (str a " <= " b " ? = " (<= a b)))))))

(deftest bin-round-trip-computes
  (testing "concrete round trips reduce: to-nat (from-nat k) = k"
    (let [e @env
          eqk (fn [k] (f/equality tl nat (c 'bin/to-nat (c 'bin/from-nat (numeral k))) (numeral k)))
          refl (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))]
      (doseq [k [0 1 2 5]]
        (is (checks? e (refl k) (eqk k)) (str "round-trip " k))))))

(deftest bin-operations-are-magnitude-independent
  (testing "Bin operations reduce in O(number of digits), independent of the
            represented VALUE. 2^40 = bin-even^40 (bin-odd bin-zero) has to-nat ~1e12
            -- utterly unreachable as a unary Nat -- yet bit-length AND the hot
            comparison bin/at-most (the actual LP-checker operation) both check
            essentially instantly. This is the point of Bin, and the concrete
            demonstration of brick 5a: the magnitude ceiling that walls unary Nat is
            gone for natively-Bin numerals. (NOTE: bin-even^k bin-zero would be VALUE
            0 -- the non-canonical zero -- so a genuine 2^k needs the trailing bin-odd
            for the low 1 bit.)"
    (let [e @env
          pow2 (fn [k] (nth (iterate be (bo bz)) k))     ; be^k (bo bz) = 2^k, to-nat = 2^k
          bit-length (fn [b] (c 'bin/bit-length b))
          at-most (fn [a b] (c 'bin/at-most a b))
          bval (fn [t] (if t (f/const* 'data/true []) (f/const* 'data/false [])))
          refln (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))
          reflb (fn [t] (f/app (f/const* 'equality/reflexive [tl]) (f/const* 'data/Bool []) (bval t)))
          eqn (fn [b k] (f/equality tl nat (bit-length b) (numeral k)))
          eqcmp (fn [a b t] (f/equality tl (f/const* 'data/Bool []) (at-most a b) (bval t)))]
      ;; 2^40 = be^40 (bo bz) has 41 digit constructors; bit-length is 41
      (is (checks? e (refln 41) (eqn (pow2 40) 41))
          "bit-length(2^40) = 41 -- magnitude 2^40 is unreachable in unary, O(41) in Bin")
      ;; the HOT operation: comparison at 2^40..2^41 scale, magnitude-independent
      (is (checks? e (reflb true)  (eqcmp (pow2 40) (pow2 40) true))  "2^40 <= 2^40")
      (is (checks? e (reflb true)  (eqcmp (pow2 40) (pow2 41) true))  "2^40 <= 2^41")
      (is (checks? e (reflb false) (eqcmp (pow2 41) (pow2 40) false)) "2^41 <= 2^40 is false"))))

(defn- to-nat [b] (c 'bin/to-nat b))

(deftest bin-to-nat-interprets-values
  (testing "bin/to-nat maps binary numerals to their Nat value (bit patterns MSB-first
            via nested constructors): bin-odd h = 2*(to-nat h)+1, bin-even h = 2*(to-nat h)"
    (let [e @env
          eqn (fn [b k] (f/equality tl nat (to-nat b) (numeral k)))
          refl (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))]
      (is (checks? e (refl 0) (eqn bz 0)) "to-nat 0")
      (is (checks? e (refl 1) (eqn (bo bz) 1)) "to-nat 1")
      (is (checks? e (refl 2) (eqn (be (bo bz)) 2)) "to-nat 2")
      ;; 5 = bin-odd(bin-even(bin-odd bin-zero))
      (is (checks? e (refl 5) (eqn (bo (be (bo bz))) 5)) "to-nat 5")
      ;; 6 = bin-even(bin-odd(bin-odd bin-zero))
      (is (checks? e (refl 6) (eqn (be (bo (bo bz))) 6)) "to-nat 6"))))

(deftest bin-recursor-reduces
  (testing "Bin.rec reduces: constructor-count folds a concrete Bin to the right Nat"
    (let [e @env
          eqn (fn [b k] (f/equality tl nat (constructor-count b) (numeral k)))
          refl (fn [k] (f/app (f/const* 'equality/reflexive [tl]) nat (numeral k)))]
      ;; bin-zero -> 0
      (is (checks? e (refl 0) (eqn bz 0)))
      ;; one non-zero constructor -> 1
      (is (checks? e (refl 1) (eqn (bo bz) 1)))
      ;; bo(be(bo bz)) -> three non-zero constructors -> 3
      (is (checks? e (refl 3) (eqn (bo (be (bo bz))) 3))))))
