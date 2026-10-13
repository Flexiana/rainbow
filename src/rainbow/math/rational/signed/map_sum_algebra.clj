(ns rainbow.math.rational.signed.map-sum-algebra
  "Algebra of signed finite sums: congruence, splitting, and the weighted bound.

    signed/add-respects-equivalence  : a~a' -> b~b' -> a+b ~ a'+b'
    signed/add-four-reorder          : (a+b)+(c+d) ~ (a+c)+(b+d)
    signed/map-sum-respects-equivalence : pointwise ~ lifts to the sum
    signed/map-sum-zero              : a sum of zeros ~ 0
    signed/map-sum-add               : sum of (f+g) ~ sum f + sum g
    signed/weighted-sum-monotone     : nonnegative weights preserve <=

  Signed addition, like nnrat addition, is associative and commutative only up
  to equivalence -- (a+b)+c and a+(b+c) are different Grothendieck pairs -- so
  every regrouping law here is stated with `signed/equivalent` and the two
  reorderings are proved componentwise from `nnrat/add-four-reorder`.

  `signed/weighted-sum-monotone` is the headline: with nonnegative weights,
  termwise domination survives weighting and summation.  That is the signed
  analogue of `nnrat/weighted-sum-monotone`, and it is what bounds a signed
  objective by a signed dual expression -- the leg of any linear-programming or
  expectation bound whose data may be negative.  It is only reachable now that
  `signed/multiply-left-monotone` exists to scale a single term.

  Native and axiom-free; chains signed finite sums and signed multiplicative
  monotonicity on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.list-sum :as sum]
            [rainbow.math.rational.signed.multiply-monotone :as mono]
            [rainbow.math.rational.signed.unit-laws :as unit]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c first second))
(defn- rat-four [a b c d]
  (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))

;; `seq-equiv a 0` unfolds to (Pa + 0) ~ (0 + Na); stripping the two paddings
;; turns it into the component statement Pa ~ Na, and back.
(defn- rat-add-zero-right [v]
  (app (function/const* 'nnrat/add-zero-right []) v))
(defn- rat-add-zero-left [v]
  (app (function/const* 'nnrat/add-zero-left []) v))

(defn- strip-zero [a h]
  (rat-trans (pos a) (radd (pos a) nnrat-zero) (neg a)
             (rat-sym (radd (pos a) nnrat-zero) (pos a)
                      (rat-add-zero-right (pos a)))
             (rat-trans (radd (pos a) nnrat-zero) (radd nnrat-zero (neg a)) (neg a)
                        h (rat-add-zero-left (neg a)))))

(defn- unstrip-zero [a h]
  (rat-trans (radd (pos a) nnrat-zero) (pos a) (radd nnrat-zero (neg a))
             (rat-add-zero-right (pos a))
             (rat-trans (pos a) (neg a) (radd nnrat-zero (neg a))
                        h
                        (rat-sym (radd nnrat-zero (neg a)) (neg a)
                                 (rat-add-zero-left (neg a))))))

(defn- signed-equiv-reflexive [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))
(defn- signed-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'signed/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- signed-four [a b c d]
  (app (function/const* 'signed/add-four-reorder []) a b c d))
(defn- signed-map-sum-monotone [A f g hfg xs]
  (app (function/const* 'signed/map-sum-monotone [U]) A f g hfg xs))
(defn- signed-multiply-left-monotone [c a b hc hab]
  (app (function/const* 'signed/multiply-left-monotone []) c a b hc hab))
(defn- signed-at-most-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-at-most-antisymmetric [a b ab ba]
  (app (function/const* 'signed/at-most-antisymmetric []) a b ab ba))
(defn- signed-equivalent-to-at-most [a b same]
  (app (function/const* 'signed/equivalent-to-at-most []) a b same))
;; signed equivalence IS an nnrat equivalence of the two cross sums, so nnrat
;; symmetry serves as signed symmetry with no new alias.
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))
(defn- signed-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))

;; a ~ a' and b ~ b' give a+b ~ a'+b'.  Unfolded the goal is
;;   (Pa+Pb) + (Na'+Nb')  ~  (Pa'+Pb') + (Na+Nb),
;; and four-term reordering turns each side into the pairing (Pa+Na')+(Pb+Nb')
;; on which the two hypotheses act directly.
(def add-respects-equivalence-spec
  {:name 'signed/add-respects-equivalence :universes []
   :type (function/forall
          [['a signed] ['ah signed] ['b signed] ['bh signed]
           ['same-a (seq-equiv 'a 'ah)] ['same-b (seq-equiv 'b 'bh)]]
          (seq-equiv (sadd 'a 'b) (sadd 'ah 'bh)))
   :value
   (function/lam
    [['a signed] ['ah signed] ['b signed] ['bh signed]
     ['same-a (seq-equiv 'a 'ah)] ['same-b (seq-equiv 'b 'bh)]]
    (let [Pa (pos 'a) Na (neg 'a) Pah (pos 'ah) Nah (neg 'ah)
          Pb (pos 'b) Nb (neg 'b) Pbh (pos 'bh) Nbh (neg 'bh)
          goal-left (radd (radd Pa Pb) (radd Nah Nbh))
          goal-right (radd (radd Pah Pbh) (radd Na Nb))
          core-left (radd (radd Pa Nah) (radd Pb Nbh))
          core-right (radd (radd Pah Na) (radd Pbh Nb))
          core (rat-add-respects (radd Pa Nah) (radd Pah Na)
                                 (radd Pb Nbh) (radd Pbh Nb)
                                 'same-a 'same-b)]
      (rat-trans goal-left core-left goal-right
                 (rat-four Pa Pb Nah Nbh)
                 (rat-trans core-left core-right goal-right
                            core
                            (rat-sym goal-right core-right
                                     (rat-four Pah Pbh Na Nb))))))})

;; (a+b)+(c+d) ~ (a+c)+(b+d), componentwise.
(def add-four-reorder-spec
  {:name 'signed/add-four-reorder :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed] ['d signed]]
          (seq-equiv (sadd (sadd 'a 'b) (sadd 'c 'd))
                     (sadd (sadd 'a 'c) (sadd 'b 'd))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed] ['d signed]]
    (let [left (sadd (sadd 'a 'b) (sadd 'c 'd))
          right (sadd (sadd 'a 'c) (sadd 'b 'd))
          p-same (rat-four (pos 'a) (pos 'b) (pos 'c) (pos 'd))
          n-same (rat-four (neg 'a) (neg 'b) (neg 'c) (neg 'd))]
      (rat-add-respects (pos left) (pos right) (neg right) (neg left)
                        p-same
                        (rat-sym (neg left) (neg right) n-same))))})

(def map-sum-respects-spec
  {:name 'signed/map-sum-respects-equivalence :universes ['u]
   :type (function/forall
          [['A type-u]
           ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
           ['hfg (function/forall [['x 'A]] (seq-equiv (app 'f 'x) (app 'g 'x)))]
           ['xs (list-of 'A)]]
          (seq-equiv (map-sum 'A 'f 'xs) (map-sum 'A 'g 'xs)))
   :value
   (function/lam
    [['A type-u]
     ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
     ['hfg (function/forall [['x 'A]] (seq-equiv (app 'f 'x) (app 'g 'x)))]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam [['ys (list-of 'A)]]
                       (seq-equiv (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys)))
         (signed-equiv-reflexive signed-zero)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (seq-equiv (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail))]]
          (signed-add-respects (app 'f 'head) (app 'g 'head)
                               (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
                               (app 'hfg 'head) 'ih))
         'xs))})

;; A sum whose every term is zero is zero: each cons step is 0 + 0 ~ 0.
(def map-sum-zero-spec
  {:name 'signed/map-sum-zero :universes ['u]
   :type (function/forall
          [['A type-u]
           ['f (function/arrow 'A signed)]
           ['hf (function/forall [['x 'A]] (seq-equiv (app 'f 'x) signed-zero))]
           ['xs (list-of 'A)]]
          (seq-equiv (map-sum 'A 'f 'xs) signed-zero))
   :value
   (function/lam
    [['A type-u]
     ['f (function/arrow 'A signed)]
     ['hf (function/forall [['x 'A]] (seq-equiv (app 'f 'x) signed-zero))]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam [['ys (list-of 'A)]]
                       (seq-equiv (map-sum 'A 'f 'ys) signed-zero))
         (signed-equiv-reflexive signed-zero)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (seq-equiv (map-sum 'A 'f 'tail) signed-zero)]]
          (let [total (sadd (app 'f 'head) (map-sum 'A 'f 'tail))]
            (unstrip-zero
             total
             (rat-add-respects
              (pos (app 'f 'head)) (neg (app 'f 'head))
              (pos (map-sum 'A 'f 'tail)) (neg (map-sum 'A 'f 'tail))
              (strip-zero (app 'f 'head) (app 'hf 'head))
              (strip-zero (map-sum 'A 'f 'tail) 'ih)))))
         'xs))})

(def weighted-sum-monotone-spec
  {:name 'signed/weighted-sum-monotone :universes ['u]
   :type (function/forall
          [['A type-u]
           ['w (function/arrow 'A signed)]
           ['x (function/arrow 'A signed)] ['y (function/arrow 'A signed)]
           ['hw (function/forall [['i 'A]] (sle signed-zero (app 'w 'i)))]
           ['hxy (function/forall [['i 'A]] (sle (app 'x 'i) (app 'y 'i)))]
           ['idx (list-of 'A)]]
          (sle (map-sum 'A (function/lam [['i 'A]]
                                         (smul (app 'w 'i) (app 'x 'i))) 'idx)
               (map-sum 'A (function/lam [['i 'A]]
                                         (smul (app 'w 'i) (app 'y 'i))) 'idx)))
   :value
   (function/lam
    [['A type-u]
     ['w (function/arrow 'A signed)]
     ['x (function/arrow 'A signed)] ['y (function/arrow 'A signed)]
     ['hw (function/forall [['i 'A]] (sle signed-zero (app 'w 'i)))]
     ['hxy (function/forall [['i 'A]] (sle (app 'x 'i) (app 'y 'i)))]
     ['idx (list-of 'A)]]
    (signed-map-sum-monotone
     'A
     (function/lam [['i 'A]] (smul (app 'w 'i) (app 'x 'i)))
     (function/lam [['i 'A]] (smul (app 'w 'i) (app 'y 'i)))
     (function/lam
      [['i 'A]]
      (signed-multiply-left-monotone (app 'w 'i) (app 'x 'i) (app 'y 'i)
                                     (app 'hw 'i) (app 'hxy 'i)))
     'idx))})

;; Signed equivalence is transitive.  It is NOT an nnrat equivalence between the
;; same pair of terms at each step, so nnrat transitivity does not apply
;; directly; instead each equivalence is split into its two order directions,
;; those are chained by signed order transitivity, and antisymmetry rebuilds the
;; equivalence.
(def equivalent-transitive-spec
  {:name 'signed/equivalent-transitive :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]
           ['ab (seq-equiv 'a 'b)] ['bc (seq-equiv 'b 'c)]]
          (seq-equiv 'a 'c))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]
     ['ab (seq-equiv 'a 'b)] ['bc (seq-equiv 'b 'c)]]
    (signed-at-most-antisymmetric
     'a 'c
     (signed-at-most-transitive
      'a 'b 'c
      (signed-equivalent-to-at-most 'a 'b 'ab)
      (signed-equivalent-to-at-most 'b 'c 'bc))
     (signed-at-most-transitive
      'c 'b 'a
      (signed-equivalent-to-at-most 'c 'b (signed-sym 'b 'c 'bc))
      (signed-equivalent-to-at-most 'b 'a (signed-sym 'a 'b 'ab)))))})

;; sum of (f + g) ~ sum f + sum g.  The cons step regroups
;; (f h + g h) + (Sf t + Sg t)  into  (f h + Sf t) + (g h + Sg t).
(def map-sum-add-spec
  {:name 'signed/map-sum-add :universes ['u]
   :type (function/forall
          [['A type-u]
           ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
           ['xs (list-of 'A)]]
          (seq-equiv
           (map-sum 'A (function/lam [['i 'A]]
                                     (sadd (app 'f 'i) (app 'g 'i))) 'xs)
           (sadd (map-sum 'A 'f 'xs) (map-sum 'A 'g 'xs))))
   :value
   (function/lam
    [['A type-u]
     ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
     ['xs (list-of 'A)]]
    (let [combined (function/lam [['i 'A]] (sadd (app 'f 'i) (app 'g 'i)))]
      (app (function/const* 'data/List.rec [data-level zero-level])
           'A
           (function/lam
            [['ys (list-of 'A)]]
            (seq-equiv (map-sum 'A combined 'ys)
                       (sadd (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys))))
           ;; nil : 0 ~ 0 + 0
           (signed-sym (sadd signed-zero signed-zero) signed-zero
                       (signed-add-zero-right signed-zero))
           (function/lam
            [['head 'A] ['tail (list-of 'A)]
             ['ih (seq-equiv (map-sum 'A combined 'tail)
                             (sadd (map-sum 'A 'f 'tail)
                                   (map-sum 'A 'g 'tail)))]]
            (let [fh (app 'f 'head) gh (app 'g 'head)
                  ft (map-sum 'A 'f 'tail) gt (map-sum 'A 'g 'tail)
                  start (sadd (sadd fh gh) (map-sum 'A combined 'tail))
                  middle (sadd (sadd fh gh) (sadd ft gt))
                  finish (sadd (sadd fh ft) (sadd gh gt))]
              (signed-trans
               start middle finish
               (signed-add-respects (sadd fh gh) (sadd fh gh)
                                    (map-sum 'A combined 'tail) (sadd ft gt)
                                    (signed-equiv-reflexive (sadd fh gh)) 'ih)
               (signed-four fh gh ft gt))))
           'xs)))})

(def definition-specs [])
(def theorem-specs
  [add-respects-equivalence-spec
   add-four-reorder-spec
   equivalent-transitive-spec
   map-sum-respects-spec
   map-sum-zero-spec
   map-sum-add-spec
   weighted-sum-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.unit-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-map-sum-algebra theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.map-sum-algebra))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
