(ns rainbow.math.rational.signed.convex-optimality
  "First-order optimality for convex objectives over signed rationals.

  A convex objective `f` admits, at a candidate point `x0`, a supporting linear
  certificate `linear` (the subgradient form `x |-> <g0, x - x0>`) with

      f x0 + linear x  <=  f x        for every feasible x.

  The variational inequality at `x0` says that certificate never points downhill
  inside the feasible set:

      0 <= linear x                   for every feasible x.

  Together these give global optimality of `x0` -- no local reasoning, no
  descent argument, no derivative calculus:

      f x0 = f x0 + 0 <= f x0 + linear x <= f x.

  This is the reason convex programs have no spurious local minima, and it is
  the soundness core of every optimality certificate a solver can emit.  The
  linear certificate is kept abstract as a function, so no signed multiplication
  or inner product is postulated; instantiating `linear` at an inner product
  recovers the textbook statement.

  Also proved: convex certificates add (so the certificate for a sum of convex
  objectives is the sum of the certificates), and the sum of two certified
  stationary objectives is globally minimized at the shared point.

  Native and axiom-free; chains the D63 signed order toolkit through signed
  limit uniqueness (for signed/add-zero-right) and signed order monotonicity."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def signed (function/const* 'signed/SignedRational []))
(def objective (function/arrow signed signed))
(def predicate (function/arrow signed 'Prop))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- rat-four [a b c d]
  (app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- rat-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       a ah b bh same-a same-b))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-add-left-monotone [a b c ordered]
  (app (function/const* 'signed/add-left-monotone []) a b c ordered))
(defn- signed-add-monotone [a ah b bh ordered-a ordered-b]
  (app (function/const* 'signed/add-monotone []) a ah b bh ordered-a ordered-b))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))

;; (a+b)+(c+d) is signed-equivalent to (a+c)+(b+d), componentwise.  Rebuilt
;; locally from the nnrat reassociation law so this module introduces no new
;; alias and depends only on the chained order toolkit.
(defn- signed-add-four-reorder [a b c d]
  (let [left (sadd (sadd a b) (sadd c d))
        right (sadd (sadd a c) (sadd b d))
        p-same (rat-four (pos a) (pos b) (pos c) (pos d))
        n-same (rat-four (neg a) (neg b) (neg c) (neg d))]
    (rat-add-respects (pos left) (pos right) (neg right) (neg left)
                      p-same
                      (rat-sym (neg left) (neg right) n-same))))

;; The certificate is what makes x0 globally optimal: pad f x0 with zero, raise
;; the zero to `linear x` by the variational inequality, then discharge with
;; the convexity certificate.
(def first-order-global-minimum-spec
  {:name 'optimization/signed-first-order-global-minimum :universes []
   :type
   (function/forall
    [['f objective] ['linear objective] ['x0 signed] ['feasible predicate]
     ['certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'linear 'x)) (app 'f 'x)))]
     ['variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'linear 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (app 'f 'x0) (app 'f 'x)))
   :value
   (function/lam
    [['f objective] ['linear objective] ['x0 signed] ['feasible predicate]
     ['certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'linear 'x)) (app 'f 'x)))]
     ['variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'linear 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (let [base (app 'f 'x0)
          step (app 'linear 'x)
          padded (sadd base signed-zero)
          raised (sadd base step)
          ;; base + 0 <= base + linear x
          padded<=raised
          (signed-add-left-monotone signed-zero step base
                                    (app 'variational 'x 'member))
          ;; drop the padding: base ~ base + 0 reversed by add-zero-right
          base<=raised
          (signed-at-most-respects padded base raised raised
                                   (signed-add-zero-right base)
                                   (signed-refl raised)
                                   padded<=raised)]
      (signed-transitive base raised (app 'f 'x)
                         base<=raised
                         (app 'certificate 'x 'member))))})

;; Convex certificates add: summing the two supporting inequalities and
;; regrouping gives the supporting inequality of the summed objective, whose
;; certificate is the sum of the certificates.
(def certificate-sum-spec
  {:name 'optimization/signed-convex-certificate-sum :universes []
   :type
   (function/forall
    [['f objective] ['g objective]
     ['lf objective] ['lg objective]
     ['x0 signed] ['feasible predicate]
     ['f-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'lf 'x)) (app 'f 'x)))]
     ['g-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'g 'x0) (app 'lg 'x)) (app 'g 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (sadd (sadd (app 'f 'x0) (app 'g 'x0))
               (sadd (app 'lf 'x) (app 'lg 'x)))
         (sadd (app 'f 'x) (app 'g 'x))))
   :value
   (function/lam
    [['f objective] ['g objective]
     ['lf objective] ['lg objective]
     ['x0 signed] ['feasible predicate]
     ['f-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'lf 'x)) (app 'f 'x)))]
     ['g-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'g 'x0) (app 'lg 'x)) (app 'g 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (let [f0 (app 'f 'x0) g0 (app 'g 'x0)
          lfx (app 'lf 'x) lgx (app 'lg 'x)
          fx (app 'f 'x) gx (app 'g 'x)
          raw (sadd (sadd f0 lfx) (sadd g0 lgx))
          grouped (sadd (sadd f0 g0) (sadd lfx lgx))
          summed (signed-add-monotone
                  (sadd f0 lfx) fx (sadd g0 lgx) gx
                  (app 'f-certificate 'x 'member)
                  (app 'g-certificate 'x 'member))]
      (signed-at-most-respects raw grouped (sadd fx gx) (sadd fx gx)
                               (signed-add-four-reorder f0 lfx g0 lgx)
                               (signed-refl (sadd fx gx))
                               summed)))})

;; Two certified stationary objectives share a global minimizer: their
;; certificates add, the two variational inequalities add (0+0 collapses to 0),
;; and the first-order theorem closes it.
(def sum-global-minimum-spec
  {:name 'optimization/signed-convex-sum-global-minimum :universes []
   :type
   (function/forall
    [['f objective] ['g objective]
     ['lf objective] ['lg objective]
     ['x0 signed] ['feasible predicate]
     ['f-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'lf 'x)) (app 'f 'x)))]
     ['g-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'g 'x0) (app 'lg 'x)) (app 'g 'x)))]
     ['f-variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'lf 'x)))]
     ['g-variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'lg 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (sadd (app 'f 'x0) (app 'g 'x0))
         (sadd (app 'f 'x) (app 'g 'x))))
   :value
   (function/lam
    [['f objective] ['g objective]
     ['lf objective] ['lg objective]
     ['x0 signed] ['feasible predicate]
     ['f-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'f 'x0) (app 'lf 'x)) (app 'f 'x)))]
     ['g-certificate
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle (sadd (app 'g 'x0) (app 'lg 'x)) (app 'g 'x)))]
     ['f-variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'lf 'x)))]
     ['g-variational
      (function/forall
       [['x signed] ['member (app 'feasible 'x)]]
       (sle signed-zero (app 'lg 'x)))]
     ['x signed] ['member (app 'feasible 'x)]]
    (let [sum-objective
          (function/lam [['y signed]] (sadd (app 'f 'y) (app 'g 'y)))
          sum-linear
          (function/lam [['y signed]] (sadd (app 'lf 'y) (app 'lg 'y)))
          sum-certificate
          (function/lam
           [['y signed] ['member-y (app 'feasible 'y)]]
           (app (function/const*
                 'optimization/signed-convex-certificate-sum [])
                'f 'g 'lf 'lg 'x0 'feasible
                'f-certificate 'g-certificate 'y 'member-y))
          sum-variational
          (function/lam
           [['y signed] ['member-y (app 'feasible 'y)]]
           (let [both (signed-add-monotone
                       signed-zero (app 'lf 'y)
                       signed-zero (app 'lg 'y)
                       (app 'f-variational 'y 'member-y)
                       (app 'g-variational 'y 'member-y))
                 target (sadd (app 'lf 'y) (app 'lg 'y))]
             (signed-at-most-respects
              (sadd signed-zero signed-zero) signed-zero target target
              (signed-add-zero-right signed-zero)
              (signed-refl target)
              both)))]
      (app (function/const*
            'optimization/signed-first-order-global-minimum [])
           sum-objective sum-linear 'x0 'feasible
           sum-certificate sum-variational 'x 'member)))})

(def definition-specs [])
(def theorem-specs
  [first-order-global-minimum-spec
   certificate-sum-spec
   sum-global-minimum-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.order-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-convex-optimality theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.convex-optimality))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
