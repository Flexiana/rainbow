(ns rainbow.math.rational.nnrat.map-sum-additive
  "Additive congruences for nnrat/map-sum, up to nnrat equivalence (~) -- the
  Fubini prerequisites.  nnrat addition only associates/commutes up to ~ (the
  groupings give equal-by-nat-identity but syntactically distinct denominators),
  so these are equivalences, bridged to <= later by at-most-respects-equivalence:

    nnrat/map-sum-zero : map-sum (\\_.0) is ~ 0
    nnrat/map-sum-add  : map-sum (\\i. f i + g i) is ~ map-sum f is + map-sum g is

  Both by List.rec induction: nil is reflexive (empty sum reduces to 0); the cons
  case pushes the head term out with nnrat/add-respects-equivalence + the IH and,
  for map-sum-add, the four-term reorder (a+b)+(c+d) ~ (a+c)+(b+d).  Polymorphic
  in the element type.  Native and axiom-free; chains nnrat-list-sum and
  nnrat-additive-reassociation on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.list-sum :as ls]
            [rainbow.math.rational.nnrat.additive-reassociation :as ar]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l l-eq r r-eq same-l same-r]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l l-eq r r-eq same-l same-r))
(defn- add-four-reorder [a b c d]
  (function/app (function/const* 'nnrat/add-four-reorder []) a b c d))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- app [f x] (function/app f x))

;; the constant-zero mapping and the pointwise-sum mapping
(defn- zero-map [] (function/lam [['i 'A]] nnrat-zero))
(defn- sum-map [f g] (function/lam [['i 'A]] (radd (app f 'i) (app g 'i))))

;; map-sum (\_.0) is ~ 0
(def map-sum-zero-spec
  {:name 'nnrat/map-sum-zero :universes ['u]
   :type (function/forall [['A type-u] ['is (list-of 'A)]]
                          (equiv (map-sum 'A (zero-map) 'is) nnrat-zero))
   :value
   (function/lam
    [['A type-u] ['is (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['ys (list-of 'A)]] (equiv (map-sum 'A (zero-map) 'ys) nnrat-zero))
     ;; nil : map-sum (\_.0) nil = 0 ~ 0
     (equiv-refl nnrat-zero)
     ;; cons head tail : (0 + Mt) ~ 0 where Mt = map-sum (\_.0) tail ~ 0 (IH)
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (equiv (map-sum 'A (zero-map) 'tail) nnrat-zero)]]
      (equiv-trans (radd nnrat-zero (map-sum 'A (zero-map) 'tail))
                   (radd nnrat-zero nnrat-zero)
                   nnrat-zero
                   (add-respects nnrat-zero nnrat-zero
                                 (map-sum 'A (zero-map) 'tail) nnrat-zero
                                 (equiv-refl nnrat-zero) 'ih)
                   (equiv-refl nnrat-zero)))       ; (0+0) ~ 0  (0+0 reduces to 0)
     'is))})

;; map-sum (\i. f i + g i) is ~ map-sum f is + map-sum g is
(def map-sum-add-spec
  {:name 'nnrat/map-sum-add :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
           ['is (list-of 'A)]]
          (equiv (map-sum 'A (sum-map 'f 'g) 'is)
                 (radd (map-sum 'A 'f 'is) (map-sum 'A 'g 'is))))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
     ['is (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['ys (list-of 'A)]]
                   (equiv (map-sum 'A (sum-map 'f 'g) 'ys)
                          (radd (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys))))
     ;; nil : 0 ~ (0 + 0)
     (equiv-refl nnrat-zero)
     ;; cons head tail
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (equiv (map-sum 'A (sum-map 'f 'g) 'tail)
                   (radd (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)))]]
      (let [fh (app 'f 'head) gh (app 'g 'head)
            sf (map-sum 'A 'f 'tail) sg (map-sum 'A 'g 'tail)
            lt (map-sum 'A (sum-map 'f 'g) 'tail)]
        ;; ((fh+gh)+lt) ~ ((fh+gh)+(sf+sg)) ~ ((fh+sf)+(gh+sg))
        (equiv-trans (radd (radd fh gh) lt)
                     (radd (radd fh gh) (radd sf sg))
                     (radd (radd fh sf) (radd gh sg))
                     (add-respects (radd fh gh) (radd fh gh) lt (radd sf sg)
                                   (equiv-refl (radd fh gh)) 'ih)
                     (add-four-reorder fh gh sf sg))))
     'is))})

(def definition-specs [])
(def theorem-specs [map-sum-zero-spec map-sum-add-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.list-sum rainbow.math.rational.nnrat.additive-reassociation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-map-sum-additive (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.map-sum-additive))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
