(ns rainbow.math.rational.signed.map-sum-scale
  "Nonnegative-rational scaling of signed indexed sums and bilinear objectives.
  Produces the endpoint equivalences for formal LP D^2/D scaling, including
  empty and repeated-index lists. Host-language input transformation is not
  identified with this formal expression without a separate correspondence."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.map-sum-algebra :as sums]
            [rainbow.math.rational.signed.scale-additive :as additive]
            [rainbow.math.linear.vector.dot-scale :as dot-scale]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def signed (f/const* 'signed/SignedRational []))
(def signed-zero (f/const* 'signed/zero []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- list-of [A] (f/app (f/const* 'data/List [data-level]) A))
(defn- scale [c x] (app 'signed/scale c x))
(defn- add [x y] (app 'signed/add x y))
(defn- mul [x y] (app 'signed/multiply x y))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- sum [A mapping xs] (poly 'signed/map-sum A mapping xs))
(defn- pos [x] (app 'signed/positive x))
(defn- neg [x] (app 'signed/negative x))
(defn- sym [x y h]
  (app 'nnrat/equivalent-symmetric
       (ring/radd (pos x) (neg y)) (ring/radd (pos y) (neg x)) h))
(defn- trans [x y z hxy hyz]
  (app 'signed/equivalent-transitive x y z hxy hyz))
(defn- scaled-mapping [A c mapping]
  (f/lam [['i A]] (scale c (f/app mapping 'i))))
(defn- products [A left right]
  (f/lam [['i A]] (mul (f/app left 'i) (f/app right 'i))))

(def map-sum-nnrat-scale-spec
  {:name 'signed/map-sum-nnrat-scale :universes ['u]
   :type
   (f/forall [['A type-u] ['c nnrat] ['mapping (f/arrow 'A signed)]
              ['xs (list-of 'A)]]
             (eqv (sum 'A (scaled-mapping 'A 'c 'mapping) 'xs)
                  (scale 'c (sum 'A 'mapping 'xs))))
   :value
   (f/lam
    [['A type-u] ['c nnrat] ['mapping (f/arrow 'A signed)] ['xs (list-of 'A)]]
    (let [scaled (scaled-mapping 'A 'c 'mapping)]
      (f/app
       (f/const* 'data/List.rec [data-level [:zero]]) 'A
       (f/lam [['ys (list-of 'A)]]
              (eqv (sum 'A scaled 'ys) (scale 'c (sum 'A 'mapping 'ys))))
       (sym (scale 'c signed-zero) signed-zero (app 'signed/scale-zero 'c))
       (f/lam
        [['head 'A] ['tail (list-of 'A)]
         ['ih (eqv (sum 'A scaled 'tail) (scale 'c (sum 'A 'mapping 'tail)))]]
        (let [h (f/app 'mapping 'head)
              t (sum 'A 'mapping 'tail)
              sh (scale 'c h)
              st (sum 'A scaled 'tail)
              start (add sh st)
              middle (add sh (scale 'c t))
              finish (scale 'c (add h t))]
          (trans start middle finish
                 (app 'signed/add-respects-equivalence sh sh st (scale 'c t)
                      (app 'signed/equivalent-reflexive sh) 'ih)
                 (sym finish middle (app 'signed/scale-additive 'c h t)))))
       'xs)))})

(def multiply-scaled-factors-spec
  {:name 'signed/multiply-scaled-factors :universes []
   :type
   (f/forall [['a nnrat] ['b nnrat] ['x signed] ['y signed]]
             (eqv (mul (scale 'a 'x) (scale 'b 'y))
                  (scale (ring/rmul 'a 'b) (mul 'x 'y))))
   :value
   (f/lam
    [['a nnrat] ['b nnrat] ['x signed] ['y signed]]
    (let [xp (pos 'x) xn (neg 'x) yp (pos 'y) yn (neg 'y)
          lp (ring/radd (ring/rmul (ring/rmul 'a xp) (ring/rmul 'b yp))
                        (ring/rmul (ring/rmul 'a xn) (ring/rmul 'b yn)))
          ln (ring/radd (ring/rmul (ring/rmul 'a xp) (ring/rmul 'b yn))
                        (ring/rmul (ring/rmul 'a xn) (ring/rmul 'b yp)))
          rp (ring/rmul (ring/rmul 'a 'b)
                        (ring/radd (ring/rmul xp yp) (ring/rmul xn yn)))
          rn (ring/rmul (ring/rmul 'a 'b)
                        (ring/radd (ring/rmul xp yn) (ring/rmul xn yp)))]
      (ring/equiv (ring/radd lp rn) (ring/radd rp ln))))})

(def map-sum-biscaled-products-spec
  {:name 'signed/map-sum-biscaled-products :universes ['u]
   :type
   (f/forall
    [['A type-u] ['a nnrat] ['b nnrat]
     ['left (f/arrow 'A signed)] ['right (f/arrow 'A signed)] ['xs (list-of 'A)]]
    (eqv (sum 'A (products 'A (scaled-mapping 'A 'a 'left)
                          (scaled-mapping 'A 'b 'right)) 'xs)
         (scale (ring/rmul 'a 'b) (sum 'A (products 'A 'left 'right) 'xs))))
   :value
   (f/lam
    [['A type-u] ['a nnrat] ['b nnrat]
     ['left (f/arrow 'A signed)] ['right (f/arrow 'A signed)] ['xs (list-of 'A)]]
    (let [original (products 'A 'left 'right)
          scaled (products 'A (scaled-mapping 'A 'a 'left)
                           (scaled-mapping 'A 'b 'right))
          c (ring/rmul 'a 'b)
          termwise (scaled-mapping 'A c original)]
      (trans
       (sum 'A scaled 'xs) (sum 'A termwise 'xs) (scale c (sum 'A original 'xs))
       (poly 'signed/map-sum-respects-equivalence 'A scaled termwise
             (f/lam [['i 'A]]
                    (app 'signed/multiply-scaled-factors 'a 'b
                         (f/app 'left 'i) (f/app 'right 'i)))
             'xs)
       (poly 'signed/map-sum-nnrat-scale 'A c original 'xs))))})

(def lp-objective-cubic-scale-spec
  {:name 'signed/lp-objective-cubic-scale :universes ['u]
   :type
   (f/forall
    [['A type-u] ['d nnrat] ['coefficients (f/arrow 'A signed)]
     ['values (f/arrow 'A signed)] ['indices (list-of 'A)]]
    (eqv
     (sum 'A (products 'A (scaled-mapping 'A (ring/rmul 'd 'd) 'coefficients)
                       (scaled-mapping 'A 'd 'values)) 'indices)
     (scale (ring/rmul (ring/rmul 'd 'd) 'd)
            (sum 'A (products 'A 'coefficients 'values) 'indices))))
   :value
   (f/lam
    [['A type-u] ['d nnrat] ['coefficients (f/arrow 'A signed)]
     ['values (f/arrow 'A signed)] ['indices (list-of 'A)]]
    (poly 'signed/map-sum-biscaled-products 'A (ring/rmul 'd 'd) 'd
          'coefficients 'values 'indices))})

(def definition-specs [])
(def theorem-specs [map-sum-nnrat-scale-spec multiply-scaled-factors-spec
                    map-sum-biscaled-products-spec lp-objective-cubic-scale-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.scale-additive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/add-spec-shared :vector-dot-scale dot-scale/scale-zero-spec) (support/extend-with :signed-map-sum-scale theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.map-sum-scale))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
