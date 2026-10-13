(ns rainbow.math.rational.signed.multiply-associative
  "Associativity of signed multiplication, and the outer swap the LP column
  bound needs.

    signed/multiply-associative : (a*b)*c ~ a*(b*c)
    signed/multiply-swap-outer  : (p*q)*r ~ (p*r)*q

  Both are genuine eight-monomial identities.  Unfolded, `(a*b)*c ~ a*(b*c)` is
  the nnrat equivalence

    [(Pa*Pb + Na*Nb)*Pc + (Pa*Nb + Na*Pb)*Nc] + [Pa*(Pb*Nc + Nb*Pc) + Na*(Pb*Pc + Nb*Nc)]
      ~
    [Pa*(Pb*Pc + Nb*Nc) + Na*(Pb*Nc + Nb*Pc)] + [(Pa*Pb + Na*Nb)*Nc + (Pa*Nb + Na*Pb)*Pc]

  whose two sides carry the same eight degree-three monomials in eight different
  bracketings and orders.  Written by hand that is a few hundred lines of
  add-four-reorder / multiply-associative / congruence chaining; here each proof
  is a single call to `rainbow.math.rational.nnrat.ring`, which normalizes both sides to
  a canonical sorted sum of canonical monomials and refuses to emit anything if
  the multisets differ.

  `signed/multiply-swap-outer` is the specific reassociation that turns
  (A_ij * y_i) * x_j into (A_ij * x_j) * y_i, which is the step that was blocking
  the column-side discharge of signed LP weak duality.

  Native and axiom-free; chains the nnrat-ring law providers on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.multiply :as multiply]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(def ^:private radd ring/radd)
(def ^:private rmul ring/rmul)

;; the two Grothendieck components of a signed product, written out so the ring
;; tactic sees the surface expression rather than an opaque `signed/multiply`
(defn- product-positive [pl nl pr nr] (radd (rmul pl pr) (rmul nl nr)))
(defn- product-negative [pl nl pr nr] (radd (rmul pl nr) (rmul nl pr)))

;; components of (x*y)*z given the components of x, y, z
(defn- left-nested [px nx py ny pz nz]
  (let [pxy (product-positive px nx py ny)
        nxy (product-negative px nx py ny)]
    [(product-positive pxy nxy pz nz) (product-negative pxy nxy pz nz)]))

;; components of x*(y*z)
(defn- right-nested [px nx py ny pz nz]
  (let [pyz (product-positive py ny pz nz)
        nyz (product-negative py ny pz nz)]
    [(product-positive px nx pyz nyz) (product-negative px nx pyz nyz)]))

;; `signed/equivalent u v` unfolds to `positive u + negative v ~ positive v + negative u`
(defn- cross-equivalence [[pu nu] [pv nv]]
  (ring/equiv (radd pu nv) (radd pv nu)))

(def multiply-associative-spec
  {:name 'signed/multiply-associative :universes []
   :type (function/forall
          [['a signed] ['b signed] ['c signed]]
          (seq-equiv (smul (smul 'a 'b) 'c) (smul 'a (smul 'b 'c))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]]
    (let [Pa (pos 'a) Na (neg 'a)
          Pb (pos 'b) Nb (neg 'b)
          Pc (pos 'c) Nc (neg 'c)]
      (cross-equivalence (left-nested Pa Na Pb Nb Pc Nc)
                         (right-nested Pa Na Pb Nb Pc Nc))))})

(def multiply-swap-outer-spec
  {:name 'signed/multiply-swap-outer :universes []
   :type (function/forall
          [['p signed] ['q signed] ['r signed]]
          (seq-equiv (smul (smul 'p 'q) 'r) (smul (smul 'p 'r) 'q)))
   :value
   (function/lam
    [['p signed] ['q signed] ['r signed]]
    (let [Pp (pos 'p) Np (neg 'p)
          Pq (pos 'q) Nq (neg 'q)
          Pr (pos 'r) Nr (neg 'r)]
      (cross-equivalence (left-nested Pp Np Pq Nq Pr Nr)
                         (left-nested Pp Np Pr Nr Pq Nq))))})

(def definition-specs [])
(def theorem-specs [multiply-associative-spec multiply-swap-outer-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.ring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-multiply-associative theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.multiply-associative))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
