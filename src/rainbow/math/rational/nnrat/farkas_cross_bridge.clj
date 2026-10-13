(ns rainbow.math.rational.nnrat.farkas-cross-bridge
  "Piece 1 core of the n-variable capstone:
  the structured bridge recognizing a cross condition as a both-sides row.

  brick 6's cross-product core emits cross conditions with OPAQUE survivor
  blocks; the recursive reduction consumes STRUCTURED both-sides rows
  A*v+P <= B*v+Q. This bridge discharges that seam for the general AFFINE
  block case: when the eliminated variable's blocks are affine in the next
  variable w, s_hi = c_hi*w + d_hi and s_lo = c_lo*w + d_lo, a single cross
  condition

    w_lo*a_hi + s_hi*a_lo <= b_hi*a_lo + s_lo*a_hi

  IS the both-sides row A*w + P <= B*w + Q with
    A = c_hi*a_lo, P = w_lo*a_hi + d_hi*a_lo,
    B = c_lo*a_hi, Q = b_hi*a_lo + d_lo*a_hi.

  nnrat/farkas-cross-to-both-sides proves the cross condition implies that
  both-sides row (necessary direction). Each side is realigned up to nnrat
  equivalence -- distribute the block (multiply-distributes-add-right),
  fold the w-coefficient (multiply-swap-right), lift the w-term to the front
  (add-swap-right) -- and transported by at-most-respects-equivalence.
  Mapping this over the bilist cross-condition structure is what discharges
  the eliminate-round's `link`, turning the elimination round into a closed
  step of the variable-count induction. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- esym [l r same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- etrans [l m r first second]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r first second))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- add-swap-right [a b c]
  (function/app (function/const* 'nnrat/add-swap-right []) a b c))
(defn- swap-right [a b c]
  (function/app (function/const* 'nnrat/multiply-swap-right []) a b c))
(defn- distribute-right [a b m]
  (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(defn- at-most-respects [l el r er sl sr ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                l el r er sl sr ordered))

;; align one side: w_head + (c*w + d)*factor  ~  (c*factor)*w + (w_head + d*factor)
;; (w_head = w_lo*a_hi for the LHS, b_hi*a_lo for the RHS)
(defn- side-eq [w-head c w d factor]
  (let [coef (mul c factor)                       ; A (or B)
        dfac (mul d factor)                        ; d*factor
        block (add (mul c w) d)                    ; s = c*w + d
        block-fac (mul block factor)               ; s*factor
        cw-fac (mul (mul c w) factor)              ; (c*w)*factor
        ;; s*factor ~ (c*w)*factor + d*factor
        dist (distribute-right (mul c w) d factor)
        ;; (c*w)*factor ~ (c*factor)*w
        sw (swap-right c w factor)
        ;; s*factor ~ (coef*w) + d*factor
        s-eq (etrans block-fac (add cw-fac dfac) (add (mul coef w) dfac)
                     dist
                     (add-respects cw-fac (mul coef w) dfac dfac sw (erefl dfac)))
        ;; w_head + s*factor ~ w_head + ((coef*w) + d*factor)
        lifted (add-respects w-head w-head block-fac (add (mul coef w) dfac)
                             (erefl w-head) s-eq)]
    ;; ~ (coef*w) + (w_head + d*factor)
    (etrans (add w-head block-fac)
            (add w-head (add (mul coef w) dfac))
            (add (mul coef w) (add w-head dfac))
            lifted
            (add-swap-right w-head (mul coef w) dfac))))

(def cross-to-both-sides-spec
  {:name 'nnrat/farkas-cross-to-both-sides
   :universes []
   :type
   (function/forall
    [['w-lo nnrat] ['a-hi nnrat] ['a-lo nnrat] ['b-hi nnrat]
     ['c-hi nnrat] ['d-hi nnrat] ['c-lo nnrat] ['d-lo nnrat] ['w nnrat]
     ['cross (at-most
              (add (mul 'w-lo 'a-hi)
                   (mul (add (mul 'c-hi 'w) 'd-hi) 'a-lo))
              (add (mul 'b-hi 'a-lo)
                   (mul (add (mul 'c-lo 'w) 'd-lo) 'a-hi)))]]
    (at-most
     (add (mul (mul 'c-hi 'a-lo) 'w)
          (add (mul 'w-lo 'a-hi) (mul 'd-hi 'a-lo)))
     (add (mul (mul 'c-lo 'a-hi) 'w)
          (add (mul 'b-hi 'a-lo) (mul 'd-lo 'a-hi)))))
   :value
   (function/lam
    [['w-lo nnrat] ['a-hi nnrat] ['a-lo nnrat] ['b-hi nnrat]
     ['c-hi nnrat] ['d-hi nnrat] ['c-lo nnrat] ['d-lo nnrat] ['w nnrat]
     ['cross (at-most
              (add (mul 'w-lo 'a-hi)
                   (mul (add (mul 'c-hi 'w) 'd-hi) 'a-lo))
              (add (mul 'b-hi 'a-lo)
                   (mul (add (mul 'c-lo 'w) 'd-lo) 'a-hi)))]]
    (let [cross-lhs (add (mul 'w-lo 'a-hi)
                         (mul (add (mul 'c-hi 'w) 'd-hi) 'a-lo))
          cross-rhs (add (mul 'b-hi 'a-lo)
                         (mul (add (mul 'c-lo 'w) 'd-lo) 'a-hi))
          bs-lhs (add (mul (mul 'c-hi 'a-lo) 'w)
                      (add (mul 'w-lo 'a-hi) (mul 'd-hi 'a-lo)))
          bs-rhs (add (mul (mul 'c-lo 'a-hi) 'w)
                      (add (mul 'b-hi 'a-lo) (mul 'd-lo 'a-hi)))
          lhs-eq (side-eq (mul 'w-lo 'a-hi) 'c-hi 'w 'd-hi 'a-lo)
          rhs-eq (side-eq (mul 'b-hi 'a-lo) 'c-lo 'w 'd-lo 'a-hi)]
      (at-most-respects
       bs-lhs cross-lhs bs-rhs cross-rhs
       (esym cross-lhs bs-lhs lhs-eq)
       (esym cross-rhs bs-rhs rhs-eq)
       'cross)))})

(def definition-specs [])
(def theorem-specs [cross-to-both-sides-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-monotone/extend-environment
      add-reassoc/extend-environment
      distribute/extend-environment
      multiply-commute/extend-environment
      product/extend-environment
      (support/extend-with :nnrat-farkas-cross-bridge
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
