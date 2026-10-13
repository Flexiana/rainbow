(ns rainbow.math.finite.bellman-signed-approximate-optimality
  "Constructive approximate fixed points of signed Bellman optimality.

  Successive iterates of any two-sided additively contractive operator inherit
  the geometric error radius of the initial residual.  A rate-null certificate
  for that radius therefore turns the iterate at its explicit modulus into an
  approximate fixed point.  The Bellman capstone applies this interface to the
  actual runtime finite max-over-actions iterate for any signed action backup
  carrying its two-sided contraction certificate.  The existing normalized
  nnrat-transition theorem supplies exactly that certificate.

  No exact fixed point is assumed or constructed.  The witness is the actual
  finite Bellman iterate, and its residual guarantee holds pointwise over the
  entire state type.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
             :as general-convergence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- optimality-step
  [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- iterate-value
  [state action actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       state action actions fallback backup steps initial))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
(defn- harmonic-radius [index]
  (from-nnrat (app (function/const* 'nnrat/harmonic []) index)))
(defn- general-harmonic-radius [ap gp steps]
  (from-nnrat
   (app (function/const* 'nnrat/general-harmonic []) ap gp steps)))

(defn- close-at [left right epsilon state]
  (proposition/conjunction
   (sle (app left state) (sadd (app right state) epsilon))
   (sle (app right state) (sadd (app left state) epsilon))))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin []) left right first second))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- add-respects
  [left left-prime right right-prime left-same right-same]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- order-respects
  [left left-prime right right-prime left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- add-monotone
  [left left-prime right right-prime left-ordered right-ordered]
  (app (function/const* 'signed/add-monotone [])
       left left-prime right right-prime left-ordered right-ordered))

(def abstract-successive-iterate-additive-radius-spec
  (let [value-function (function/arrow 'S signed)
        sequence-type (function/arrow nat value-function)
        sequence-at (fn [steps] (app 'sequence steps))
        operator-at (fn [value] (app 'operator value))
        radius (fn [steps] (error-radius 'discount 'initial-error steps))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (close-at (sequence-at 'steps)
                    (sequence-at (succ 'steps))
                    (radius 'steps) 'state)))]
    {:name 'value/signed-abstract-successive-iterate-additive-radius
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['discount signed]
       ['initial-error signed]
       ['successor-equivalent
        (function/forall
         [['steps nat] ['state 'S]]
         (veq (app (sequence-at (succ 'steps)) 'state)
              (app (operator-at (sequence-at 'steps)) 'state)))]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at (sequence-at nat-zero) (sequence-at (succ nat-zero))
                   'initial-error 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'left 'right 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (operator-at 'left) (operator-at 'right)
                    (smul 'discount 'epsilon) 'state)))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (sequence-at 'steps) (sequence-at (succ 'steps))
                 (radius 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['discount signed]
       ['initial-error signed]
       ['successor-equivalent
        (function/forall
         [['steps nat] ['state 'S]]
         (veq (app (sequence-at (succ 'steps)) 'state)
              (app (operator-at (sequence-at 'steps)) 'state)))]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at (sequence-at nat-zero) (sequence-at (succ nat-zero))
                   'initial-error 'state))]
       ['advance
        (function/forall
         [['left value-function] ['right value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'left 'right 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (operator-at 'left) (operator-at 'right)
                    (smul 'discount 'epsilon) 'state)))]]
      (function/lam
       [['steps nat]]
       (app
        (function/const* 'data/Nat.rec [zero-level])
        motive 'initial-close
        (function/lam
         [['previous nat] ['induction-hypothesis (app motive 'previous)]]
         (function/lam
          [['state 'S]]
          (let [left (sequence-at 'previous)
                right (sequence-at (succ 'previous))
                next (sequence-at (succ (succ 'previous)))
                operator-left (operator-at left)
                operator-right (operator-at right)
                next-radius (smul 'discount (radius 'previous))
                raw (app 'advance left right (radius 'previous)
                         'induction-hypothesis 'state)
                raw-left
                (sle (app operator-left 'state)
                     (sadd (app operator-right 'state) next-radius))
                raw-right
                (sle (app operator-right 'state)
                     (sadd (app operator-left 'state) next-radius))
                left-successor (app 'successor-equivalent 'previous 'state)
                right-successor
                (app 'successor-equivalent (succ 'previous) 'state)
                operator-left-to-right
                (equivalent-symmetric
                 (app right 'state) (app operator-left 'state) left-successor)
                operator-right-to-next
                (equivalent-symmetric
                 (app next 'state) (app operator-right 'state) right-successor)
                result-left
                (order-respects
                 (app operator-left 'state) (app right 'state)
                 (sadd (app operator-right 'state) next-radius)
                 (sadd (app next 'state) next-radius)
                 operator-left-to-right
                 (add-respects
                  (app operator-right 'state) (app next 'state)
                  next-radius next-radius operator-right-to-next
                  (equivalent-reflexive next-radius))
                 (left-conjunct raw-left raw-right raw))
                result-right
                (order-respects
                 (app operator-right 'state) (app next 'state)
                 (sadd (app operator-left 'state) next-radius)
                 (sadd (app right 'state) next-radius)
                 operator-right-to-next
                 (add-respects
                  (app operator-left 'state) (app right 'state)
                  next-radius next-radius operator-left-to-right
                  (equivalent-reflexive next-radius))
                 (right-conjunct raw-left raw-right raw))]
            (conjoin
             (sle (app right 'state)
                  (sadd (app next 'state) next-radius))
             (sle (app next 'state)
                  (sadd (app right 'state) next-radius))
             result-left result-right))))
        'steps)))}))

(def rate-certificate-approximate-fixed-point-spec
  (let [value-function (function/arrow 'S signed)
        sequence-type (function/arrow nat value-function)
        sequence-at (fn [steps] (app 'sequence steps))
        operator-at (fn [value] (app 'operator value))
        steps (app 'modulus 'index)
        current (sequence-at steps)
        successor-value (sequence-at (succ steps))
        image (operator-at current)
        radius-at (app 'radius steps)
        tolerance (harmonic-radius 'index)]
    {:name 'value/signed-rate-certificate-approximate-fixed-point
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['radius (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['successor-equivalent
        (function/forall
         [['n nat] ['state 'S]]
         (veq (app (sequence-at (succ 'n)) 'state)
              (app (operator-at (sequence-at 'n)) 'state)))]
       ['successive-close
        (function/forall
         [['n nat] ['state 'S]]
         (close-at (sequence-at 'n) (sequence-at (succ 'n))
                   (app 'radius 'n) 'state))]
       ['radius-null (signed-rate-null 'radius 'modulus)]
       ['index nat] ['state 'S]]
      (close-at current image tolerance 'state))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['radius (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['successor-equivalent
        (function/forall
         [['n nat] ['state 'S]]
         (veq (app (sequence-at (succ 'n)) 'state)
              (app (operator-at (sequence-at 'n)) 'state)))]
       ['successive-close
        (function/forall
         [['n nat] ['state 'S]]
         (close-at (sequence-at 'n) (sequence-at (succ 'n))
                   (app 'radius 'n) 'state))]
       ['radius-null (signed-rate-null 'radius 'modulus)]
       ['index nat] ['state 'S]]
      (let [raw (app 'successive-close steps 'state)
            raw-left
            (sle (app current 'state)
                 (sadd (app successor-value 'state) radius-at))
            raw-right
            (sle (app successor-value 'state)
                 (sadd (app current 'state) radius-at))
            null-bounds
            (app 'radius-null 'index steps
                 (app (function/const* 'nat/at-most-reflexive []) steps))
            radius-bound
            (right-conjunct (sle signed-zero radius-at)
                            (sle radius-at tolerance) null-bounds)
            successor-same (app 'successor-equivalent steps 'state)
            left-at-radius
            (order-respects
             (app current 'state) (app current 'state)
             (sadd (app successor-value 'state) radius-at)
             (sadd (app image 'state) radius-at)
             (equivalent-reflexive (app current 'state))
             (add-respects
              (app successor-value 'state) (app image 'state)
              radius-at radius-at successor-same
              (equivalent-reflexive radius-at))
             (left-conjunct raw-left raw-right raw))
            right-at-radius
            (order-respects
             (app successor-value 'state) (app image 'state)
             (sadd (app current 'state) radius-at)
             (sadd (app current 'state) radius-at)
             successor-same
             (equivalent-reflexive (sadd (app current 'state) radius-at))
             (right-conjunct raw-left raw-right raw))
            left-radius-lift
            (add-monotone
             (app image 'state) (app image 'state)
             radius-at tolerance
             (app (function/const* 'signed/at-most-reflexive [])
                  (app image 'state))
             radius-bound)
            right-radius-lift
            (add-monotone
             (app current 'state) (app current 'state)
             radius-at tolerance
             (app (function/const* 'signed/at-most-reflexive [])
                  (app current 'state))
             radius-bound)]
        (conjoin
         (sle (app current 'state) (sadd (app image 'state) tolerance))
         (sle (app image 'state) (sadd (app current 'state) tolerance))
         (order-transitive
          (app current 'state) (sadd (app image 'state) radius-at)
          (sadd (app image 'state) tolerance)
          left-at-radius left-radius-lift)
         (order-transitive
          (app image 'state) (sadd (app current 'state) radius-at)
          (sadd (app current 'state) tolerance)
          right-at-radius right-radius-lift))))}))

(defn- concrete-objects [discount]
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat discount)
        backup
        (function/lam
         [['value value-function] ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward embedded-discount
              'value 'state 'action))
        operator
        (function/lam
         [['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step 'S 'A 'actions 'fallback backup 'value 'state)))
        sequence
        (function/lam
         [['steps nat]]
         (iterate-value
          'S 'A 'actions 'fallback backup 'steps 'initial))]
    {:value-function value-function :backup backup :operator operator
     :sequence sequence :embedded-discount embedded-discount}))

(defn- successor-equivalence [value-function backup sequence steps state]
  (let [current (app sequence steps)
        next (app sequence (succ steps))
        image
        (function/lam
         [['selected-state 'S]]
         (optimality-step
          'S 'A 'actions 'fallback backup current 'selected-state))
        successor-equality
        (app (function/const* 'value/signed-iterate-successor [U V])
             'S 'A 'actions 'fallback backup steps 'initial)]
    (app
     (function/const* 'equality/substitution [data-u])
     value-function next image successor-equality
     (function/lam
      [['candidate value-function]]
      (veq (app next state) (app 'candidate state)))
     (equivalent-reflexive (app next state)))))

(comment
  ;; Rejected experiment retained as bounded failure context.  The abstract
  ;; interfaces above check, but the fully inlined normalized-transition
  ;; specialization below exhausts the kernel beta-reduction budget while
  ;; checking concrete-successive-iterate-additive-radius-spec.  None of these
  ;; three specs is installed or claimed.  The installed Bellman specialization
  ;; lives in finite-bellman-signed-approximate-optimality-generic and keeps the
  ;; action-backup contraction certificate explicit.
(def concrete-successive-iterate-additive-radius-spec
  (let [{:keys [value-function backup operator sequence embedded-discount]}
        (concrete-objects 'discount)
        initial-image (app operator 'initial)]
    {:name 'value/nnrat-transition-signed-successive-iterate-additive-radius
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              (function/const* 'nnrat/one [])))]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial initial-image 'initial-error 'state))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (app sequence 'steps) (app sequence (succ 'steps))
                 (error-radius embedded-discount 'initial-error 'steps)
                 'state)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              (function/const* 'nnrat/one [])))]
       ['initial value-function] ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial initial-image 'initial-error 'state))]]
      (app
       (function/const*
        'value/signed-abstract-successive-iterate-additive-radius [U])
       'S operator sequence embedded-discount 'initial-error
       (function/lam
        [['steps nat] ['state 'S]]
        (successor-equivalence
         value-function backup sequence 'steps 'state))
       'initial-close
       (function/lam
        [['left value-function] ['right value-function]
         ['epsilon signed]
         ['close
          (function/forall
           [['state 'S]] (close-at 'left 'right 'epsilon 'state))]
         ['state 'S]]
        (app
         (function/const*
          'value/nnrat-transition-signed-optimality-step-additively-contractive
          [U V])
         'S 'A 'states 'actions 'transition 'reward 'discount
         'fallback 'fallback-admissible 'normalized
         'left 'right 'epsilon
         (function/lam
          [['selected-state 'S]]
          (let [both (app 'close 'selected-state)]
            (left-conjunct
             (sle (app 'left 'selected-state)
                  (sadd (app 'right 'selected-state) 'epsilon))
             (sle (app 'right 'selected-state)
                  (sadd (app 'left 'selected-state) 'epsilon))
             both)))
         (function/lam
          [['selected-state 'S]]
          (let [both (app 'close 'selected-state)]
            (right-conjunct
             (sle (app 'left 'selected-state)
                  (sadd (app 'right 'selected-state) 'epsilon))
             (sle (app 'right 'selected-state)
                  (sadd (app 'left 'selected-state) 'epsilon))
             both)))
         'state))))}))

(defn- general-binders []
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        {:keys [value-function operator]} (concrete-objects gamma)]
    [['ap nat] ['gp nat]
     ['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['actions (exact-finset-of V 'A)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A signed)]
     ['fallback (function/arrow 'S 'A)]
     ['fallback-admissible
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (app 'fallback 'state)))]
     ['normalized
      (function/forall
       [['state 'S] ['action 'A]]
       (req (nnrat-total-mass
             'S 'states (app 'transition 'state 'action))
            (function/const* 'nnrat/one [])))]
     ['initial value-function] ['initial-error signed]
     ['initial-error-nonnegative (sle signed-zero 'initial-error)]
     ['initial-bound
      (sle 'initial-error
           (general-harmonic-radius 'ap 'gp nat-zero))]
     ['initial-close
      (function/forall
       [['state 'S]]
       (close-at 'initial (app operator 'initial)
                 'initial-error 'state))]]))

(def approximate-optimality-fixed-point-general-rate-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        {:keys [value-function backup operator sequence embedded-discount]}
        (concrete-objects gamma)
        radius
        (function/lam
         [['steps nat]]
         (error-radius embedded-discount 'initial-error 'steps))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'value/nnrat-transition-signed-approximate-optimality-fixed-point-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (general-binders)
      (function/forall
       [['index nat] ['state 'S]]
       (close-at (app sequence (app modulus 'index))
                 (app operator (app sequence (app modulus 'index)))
                 (harmonic-radius 'index) 'state)))
     :value
     (function/lam
      (general-binders)
      (function/lam
       [['index nat] ['state 'S]]
       (app
        (function/const*
         'value/signed-rate-certificate-approximate-fixed-point [U])
        'S operator sequence radius modulus
        (function/lam
         [['steps nat] ['selected-state 'S]]
         (successor-equivalence
          value-function backup sequence 'steps 'selected-state))
        (app
         (function/const*
          'value/nnrat-transition-signed-successive-iterate-additive-radius
          [U V])
         'S 'A 'states 'actions 'transition 'reward gamma
         'fallback 'fallback-admissible 'normalized
         'initial 'initial-error 'initial-close)
        (app
         (function/const*
          'analysis/signed-vi-error-radius-rate-null-general [])
         'ap 'gp 'initial-error
         'initial-error-nonnegative 'initial-bound)
        'index 'state)))}))

(def approximate-optimality-fixed-point-exists-general-rate-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        {:keys [value-function operator sequence]} (concrete-objects gamma)
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))
        predicate
        (function/lam
         [['candidate value-function]]
         (function/forall
          [['state 'S]]
          (close-at 'candidate (app operator 'candidate)
                    (harmonic-radius 'index) 'state)))]
    {:name 'value/nnrat-transition-signed-approximate-optimality-fixed-point-exists-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      (into (general-binders) [['index nat]])
      (proposition/existence data-u value-function predicate))
     :value
     (function/lam
      (into (general-binders) [['index nat]])
      (app
       (function/const* 'proposition/witness [data-u])
       value-function predicate
       (app sequence (app modulus 'index))
       (function/lam
        [['state 'S]]
        (app
         (function/const*
          'value/nnrat-transition-signed-approximate-optimality-fixed-point-general-rate
          [U V])
         'ap 'gp 'S 'A 'states 'actions 'transition 'reward
         'fallback 'fallback-admissible 'normalized
         'initial 'initial-error 'initial-error-nonnegative
         'initial-bound 'initial-close 'index 'state))))}))

(def attempted-concrete-specs
  [concrete-successive-iterate-additive-radius-spec
   approximate-optimality-fixed-point-general-rate-spec
   approximate-optimality-fixed-point-exists-general-rate-spec]))

(def definition-specs [])
(def theorem-specs
  [abstract-successive-iterate-additive-radius-spec
   rate-certificate-approximate-fixed-point-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-value-iteration-general-converges])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-approximate-optimality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-approximate-optimality))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
