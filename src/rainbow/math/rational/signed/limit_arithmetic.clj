(ns rainbow.math.rational.signed.limit-arithmetic
  "Axiom-free additive arithmetic for signed-rational limits.

  The local band law is the triangle inequality in the order-band presentation:

    close L e x, close M f y  ==>  close (L+M) (e+f) (x+y).

  `analysis/converges` quantifies over every signed radius, including zero.  Thus the
  sum theorem may use radius `eps` for the first sequence and radius zero for the
  second, with modulus `Ms eps + Mt zero`; additive closeness gives radius `eps+zero`,
  and radius-equivalence transport reduces that to `eps`.  This avoids importing a
  positivity premise or postulating signed division while proving the full limit law.

  Native and axiom-free; chains the D63 signed convergence/order toolkit through
  signed limit uniqueness (for signed/add-zero-right)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def sig-seq (function/arrow nat signed))
(def modulus (function/arrow signed nat))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nat-at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- close [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))

(defn- rat-refl [v]
  (app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-trans [a b c first second]
  (app (function/const* 'nnrat/equivalent-transitive []) a b c first second))
(defn- rat-comm [a b]
  (app (function/const* 'nnrat/add-commutative []) a b))
(defn- rat-four [a b c d]
  (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- rat-add-monotone [a ah b bh ordered-a ordered-b]
  (app (function/const* 'nnrat/add-monotone [])
       a ah b bh ordered-a ordered-b))
(defn- rat-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))

(defn- conjunction [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjoin [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))
(defn- prop-left [a b both]
  (app (function/const* 'proposition/left []) a b both))
(defn- prop-right [a b both]
  (app (function/const* 'proposition/right []) a b both))

(defn- reflexive-nat [v]
  (app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- witness-nat [pred value proof]
  (app (function/const* 'proposition/witness [type-level])
       nat pred value proof))
(defn- nat-transitive [a b c ab bc]
  (app (function/const* 'nat/at-most-transitive []) a b c ab bc))

;; Two-sided monotonicity of signed addition, expanded here so this module has a
;; single dependency chain.  The signed order is an nnrat order after reduction.
(defn- signed-add-monotone [a ah b bh ordered-a ordered-b]
  (let [Pa (pos a) Na (neg a) Pah (pos ah) Nah (neg ah)
        Pb (pos b) Nb (neg b) Pbh (pos bh) Nbh (neg bh)
        core-left (radd (radd Pa Nah) (radd Pb Nbh))
        core-right (radd (radd Pah Na) (radd Pbh Nb))
        goal-left (radd (radd Pa Pb) (radd Nah Nbh))
        goal-right (radd (radd Pah Pbh) (radd Na Nb))
        core (rat-add-monotone (radd Pa Nah) (radd Pah Na)
                               (radd Pb Nbh) (radd Pbh Nb)
                               ordered-a ordered-b)]
    (rat-at-most-respects
     goal-left core-left goal-right core-right
     (rat-four Pa Pb Nah Nbh)
     (rat-four Pah Pbh Na Nb)
     core)))

;; (a+b)+(c+d) is signed-equivalent to (a+c)+(b+d), componentwise.
(defn- signed-add-four-reorder [a b c d]
  (let [left (sadd (sadd a b) (sadd c d))
        right (sadd (sadd a c) (sadd b d))
        p-left (pos left) p-right (pos right)
        n-left (neg left) n-right (neg right)
        p-same (rat-four (pos a) (pos b) (pos c) (pos d))
        n-same (rat-four (neg a) (neg b) (neg c) (neg d))]
    (rat-add-respects p-left p-right n-right n-left
                      p-same (rat-sym n-left n-right n-same))))

;; (a-e)+(b-f) is signed-equivalent to (a+b)-(e+f), componentwise.
(defn- signed-subtract-add-distributes [a e b f]
  (let [left (sadd (ssub a e) (ssub b f))
        right (ssub (sadd a b) (sadd e f))
        p-left (pos left) p-right (pos right)
        n-left (neg left) n-right (neg right)
        p-same (rat-four (pos a) (neg e) (pos b) (neg f))
        n-same (rat-four (neg a) (pos e) (neg b) (pos f))]
    (rat-add-respects p-left p-right n-right n-left
                      p-same (rat-sym n-left n-right n-same))))

;; Addition in the radius argument respects signed equivalence.
(defn- signed-add-right-respects [base e eh same]
  (let [left (sadd base e) right (sadd base eh)
        raw-left (radd (pos left) (neg right))
        grouped-left (radd (radd (pos base) (neg base))
                           (radd (pos e) (neg eh)))
        grouped-right (radd (radd (pos base) (neg base))
                            (radd (pos eh) (neg e)))
        raw-right (radd (pos right) (neg left))
        left-step (rat-four (pos base) (pos e) (neg base) (neg eh))
        middle-step
        (rat-add-respects (radd (pos base) (neg base))
                          (radd (pos base) (neg base))
                          (radd (pos e) (neg eh))
                          (radd (pos eh) (neg e))
                          (rat-refl (radd (pos base) (neg base))) same)
        right-step (rat-four (pos base) (pos eh) (neg base) (neg e))]
    (rat-trans
     raw-left grouped-left raw-right left-step
     (rat-trans grouped-left grouped-right raw-right middle-step
                (rat-sym raw-right grouped-right right-step)))))

;; Subtraction in the radius argument respects signed equivalence.
(defn- signed-subtract-right-respects [base e eh same]
  (let [left (ssub base e) right (ssub base eh)
        raw-left (radd (pos left) (neg right))
        grouped-left (radd (radd (pos base) (neg base))
                           (radd (neg e) (pos eh)))
        grouped-right (radd (radd (pos base) (neg base))
                            (radd (neg eh) (pos e)))
        raw-right (radd (pos right) (neg left))
        reversed (rat-sym (radd (pos e) (neg eh))
                          (radd (pos eh) (neg e)) same)
        tail-step
        (rat-trans
         (radd (neg e) (pos eh)) (radd (pos eh) (neg e))
         (radd (neg eh) (pos e))
         (rat-comm (neg e) (pos eh))
         (rat-trans (radd (pos eh) (neg e)) (radd (pos e) (neg eh))
                    (radd (neg eh) (pos e))
                    reversed (rat-comm (pos e) (neg eh))))
        left-step (rat-four (pos base) (neg e) (neg base) (pos eh))
        middle-step
        (rat-add-respects (radd (pos base) (neg base))
                          (radd (pos base) (neg base))
                          (radd (neg e) (pos eh))
                          (radd (neg eh) (pos e))
                          (rat-refl (radd (pos base) (neg base))) tail-step)
        right-step (rat-four (pos base) (neg eh) (neg base) (pos e))]
    (rat-trans
     raw-left grouped-left raw-right left-step
     (rat-trans grouped-left grouped-right raw-right middle-step
                (rat-sym raw-right grouped-right right-step)))))

(def close-respects-radius-equivalence-spec
  {:name 'analysis/close-respects-radius-equivalence :universes []
   :type
   (function/forall
    [['L signed] ['eps signed] ['eps-prime signed] ['x signed]
     ['same-radius (seq-equiv 'eps 'eps-prime)]
     ['bounded (close 'L 'eps 'x)]]
    (close 'L 'eps-prime 'x))
   :value
   (function/lam
    [['L signed] ['eps signed] ['eps-prime signed] ['x signed]
     ['same-radius (seq-equiv 'eps 'eps-prime)]
     ['bounded (close 'L 'eps 'x)]]
    (let [old-low (ssub 'L 'eps) new-low (ssub 'L 'eps-prime)
          old-high (sadd 'L 'eps) new-high (sadd 'L 'eps-prime)
          old-low<=x
          (prop-left (sle old-low 'x) (sle 'x old-high) 'bounded)
          x<=old-high
          (prop-right (sle old-low 'x) (sle 'x old-high) 'bounded)
          low-same
          (signed-subtract-right-respects 'L 'eps 'eps-prime 'same-radius)
          high-same
          (signed-add-right-respects 'L 'eps 'eps-prime 'same-radius)
          new-low<=x
          (signed-at-most-respects old-low new-low 'x 'x
                                  low-same (signed-refl 'x) old-low<=x)
          x<=new-high
          (signed-at-most-respects 'x 'x old-high new-high
                                  (signed-refl 'x) high-same x<=old-high)]
      (conjoin (sle new-low 'x) (sle 'x new-high)
               new-low<=x x<=new-high)))})

(def close-additive-spec
  {:name 'analysis/close-additive :universes []
   :type
   (function/forall
    [['L signed] ['eps-left signed] ['x signed]
     ['M signed] ['eps-right signed] ['y signed]
     ['x-close (close 'L 'eps-left 'x)]
     ['y-close (close 'M 'eps-right 'y)]]
    (close (sadd 'L 'M) (sadd 'eps-left 'eps-right) (sadd 'x 'y)))
   :value
   (function/lam
    [['L signed] ['eps-left signed] ['x signed]
     ['M signed] ['eps-right signed] ['y signed]
     ['x-close (close 'L 'eps-left 'x)]
     ['y-close (close 'M 'eps-right 'y)]]
    (let [x-low (ssub 'L 'eps-left) x-high (sadd 'L 'eps-left)
          y-low (ssub 'M 'eps-right) y-high (sadd 'M 'eps-right)
          sum-center (sadd 'L 'M)
          sum-radius (sadd 'eps-left 'eps-right)
          sum-value (sadd 'x 'y)
          sum-low (ssub sum-center sum-radius)
          sum-high (sadd sum-center sum-radius)
          x-low<=x (prop-left (sle x-low 'x) (sle 'x x-high) 'x-close)
          x<=x-high (prop-right (sle x-low 'x) (sle 'x x-high) 'x-close)
          y-low<=y (prop-left (sle y-low 'y) (sle 'y y-high) 'y-close)
          y<=y-high (prop-right (sle y-low 'y) (sle 'y y-high) 'y-close)
          lows<=sum
          (signed-add-monotone x-low 'x y-low 'y x-low<=x y-low<=y)
          sum<=highs
          (signed-add-monotone 'x x-high 'y y-high x<=x-high y<=y-high)
          lows-same
          (signed-subtract-add-distributes
           'L 'eps-left 'M 'eps-right)
          highs-same
          (signed-add-four-reorder 'L 'eps-left 'M 'eps-right)
          sum-low<=sum
          (signed-at-most-respects
           (sadd x-low y-low) sum-low sum-value sum-value
           lows-same (signed-refl sum-value) lows<=sum)
          sum<=sum-high
          (signed-at-most-respects
           sum-value sum-value (sadd x-high y-high) sum-high
           (signed-refl sum-value) highs-same sum<=highs)]
      (conjoin (sle sum-low sum-value) (sle sum-value sum-high)
               sum-low<=sum sum<=sum-high)))})

(def limit-sum-spec
  {:name 'analysis/limit-sum :universes []
   :type
   (function/forall
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (converges
     (function/lam [['n nat]] (sadd (app 's 'n) (app 't 'n)))
     (sadd 'L 'M)
     (function/lam [['eps signed]]
                   (nadd (app 'Ms 'eps) (app 'Mt signed-zero)))))
   :value
   (function/lam
    [['s sig-seq] ['t sig-seq] ['L signed] ['M signed]
     ['Ms modulus] ['Mt modulus]
     ['s-converges (converges 's 'L 'Ms)]
     ['t-converges (converges 't 'M 'Mt)]]
    (function/lam
     [['eps signed] ['n nat]
      ['large-enough
       (nat-at-most (nadd (app 'Ms 'eps) (app 'Mt signed-zero)) 'n)]]
     (let [ms (app 'Ms 'eps)
           mt (app 'Mt signed-zero)
           threshold (nadd ms mt)
           ms<=threshold
           (witness-nat
            (function/lam [['extra nat]] (eq-nat (nadd ms 'extra) threshold))
            mt (reflexive-nat threshold))
           mt<=threshold
           (witness-nat
            (function/lam [['extra nat]] (eq-nat (nadd mt 'extra) threshold))
            ms (app (function/const* 'nat/add-commutative []) mt ms))
           ms<=n (nat-transitive ms threshold 'n ms<=threshold 'large-enough)
           mt<=n (nat-transitive mt threshold 'n mt<=threshold 'large-enough)
           s-close (app 's-converges 'eps 'n ms<=n)
           t-close (app 't-converges signed-zero 'n mt<=n)
           added
           (app (function/const* 'analysis/close-additive [])
                'L 'eps (app 's 'n) 'M signed-zero (app 't 'n)
                s-close t-close)
           eps-plus-zero (sadd 'eps signed-zero)
           eps-plus-zero-eq-eps
           (app (function/const* 'signed/add-zero-right []) 'eps)]
       (app (function/const* 'analysis/close-respects-radius-equivalence [])
            (sadd 'L 'M) eps-plus-zero 'eps
            (sadd (app 's 'n) (app 't 'n))
            eps-plus-zero-eq-eps added))))})

(def definition-specs [])
(def theorem-specs
  [close-respects-radius-equivalence-spec
   close-additive-spec
   limit-sum-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniqueness/extend-environment
      (support/extend-with :signed-limit-arithmetic theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
