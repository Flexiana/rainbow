(ns rainbow.math.sums.admissions-block
  "A blocking indicator vanishes exactly when the student does not improve, or the college has neither vacancy nor rank improvement."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call at add mul le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.strict-indicator :as strict] [rainbow.math.sums.indicator-zero :as iz]
            [rainbow.math.sums.binary-conflicts :as binary]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(defn indicators [student-gap capacity-gap college-gap]
  [(strict/indicator s/zero student-gap) (strict/indicator capacity-gap s/zero) (strict/indicator s/zero college-gap)])
(defn encoded [student-gap capacity-gap college-gap]
  (let [[x y z] (indicators student-gap capacity-gap college-gap)] (mul x (add y z))))
(defn preferences [student-gap capacity-gap college-gap]
  (a/disj (le s/zero student-gap) (b/conjunction [(le capacity-gap s/zero) (le s/zero college-gap)])))
(def forward-spec
  (let [a 'a c 'c d 'd [x y z] (indicators a c d) yz (add y z) product (mul x yz)
        P (le s/zero a) Q (b/conjunction [(le c s/zero) (le s/zero d)]) goal (a/disj P Q)
        nx (call 'signed/strict-comparison-indicator-nonnegative s/zero a)
        ny (call 'signed/strict-comparison-indicator-nonnegative c s/zero)
        nz (call 'signed/strict-comparison-indicator-nonnegative s/zero d)
        nyz (s/le-transport (add s/zero s/zero) s/zero yz yz (call 'signed/add-zero-right s/zero) (refl yz)
              (call 'signed/add-monotone s/zero y s/zero z ny nz))
        zero (call 'signed/at-most-antisymmetric product s/zero 'nonpositive (binary/nnprod x yz nx nyz))
        parts [(eqv y s/zero) (eqv z s/zero)] split (call 'signed/nonnegative-pair-sum-zero y z ny nz 'sumzero)]
    (s/spec 'signed/admissions-block-implies-preferences
      [[a signed] [c signed] [d signed] ['nonpositive (le product s/zero)]] goal
      (a/cases (eqv x s/zero) (eqv yz s/zero) goal (call 'signed/multiply-zero-split x yz zero)
        (f/lam [['studentzero (eqv x s/zero)]]
          (call 'proposition/left-disjunct P Q (call 'signed/zero-strict-indicator-implies-order s/zero a 'studentzero)))
        (f/lam [['sumzero (eqv yz s/zero)]]
          (call 'proposition/right-disjunct P Q
            (b/conjoin [(le c s/zero) (le s/zero d)]
              [(call 'signed/zero-strict-indicator-implies-order c s/zero (b/extract parts 0 split))
               (call 'signed/zero-strict-indicator-implies-order s/zero d (b/extract parts 1 split))])))))))
(def backward-spec
  (let [a 'a c 'c d 'd [x y z] (indicators a c d) yz (add y z) product (mul x yz)
        P (le s/zero a) qs [(le c s/zero) (le s/zero d)] Q (b/conjunction qs) goal (le product s/zero)
        x0 (call 'signed/order-implies-zero-strict-indicator s/zero a 'student)
        y0 (call 'signed/order-implies-zero-strict-indicator c s/zero (b/extract qs 0 'college))
        z0 (call 'signed/order-implies-zero-strict-indicator s/zero d (b/extract qs 1 'college))
        yz0 (s/trans yz (add s/zero s/zero) s/zero (s/add-cong y s/zero z s/zero y0 z0) (call 'signed/add-zero-right s/zero))]
    (s/spec 'signed/admissions-preferences-imply-zero-block [[a signed] [c signed] [d signed] ['preferences (preferences a c d)]] goal
      (a/cases P Q goal 'preferences
        (f/lam [['student P]]
          (a/eq-le product s/zero (s/trans product (mul s/zero yz) s/zero
                                   (a/mul-cong x s/zero yz yz x0 (refl yz)) (call 'signed/multiply-zero-left yz))))
        (f/lam [['college Q]]
          (a/eq-le product s/zero (s/trans product (mul x s/zero) s/zero
                                   (a/mul-cong x x yz s/zero (refl x) yz0) (call 'signed/multiply-zero-right x))))))))
(def theorem-specs [forward-spec backward-spec])
(def deps '[rainbow.math.sums.indicator-zero rainbow.math.rational.signed.no-zero-divisors])
(defn install [env] (support/extend-with env :expr-sum-admissions-block theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.admissions-block))
