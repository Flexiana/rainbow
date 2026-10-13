(ns rainbow.math.rational.signed.clamp
  "Projection of a signed rational into a closed interval.

    clamp lower upper value = min (max lower value) upper

  For every ordered interval lower <= upper, the result lies in the interval.
  Values already in the interval are preserved up to signed equivalence; values
  below or above it saturate at the corresponding endpoint.  Clamp is monotone
  in its value argument without any interval hypothesis, and respects signed
  equivalence in all three inputs.

  These are structural lattice proofs over signed min/max.  They do not unfold
  rational arithmetic and introduce no axiom, making the operator reusable by
  projected optimization, box constraints, trust regions, and bounded monitors.
  Native and axiom-free on D63."
  (:refer-clojure :exclude [min max])
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.minmax-algebra :as algebra]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- minimum [left right]
  (app (function/const* 'signed/min []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- clamp [lower upper value]
  (app (function/const* 'signed/clamp []) lower upper value))
(defn- reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))
(defn- equivalent-to-at-most [left right same]
  ;; Transport the reflexive order left<=left along right-endpoint
  ;; equivalence.  This avoids pulling the larger signed-unit-laws dependency
  ;; chain into a structural lattice module.
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left left right
       (app (function/const* 'signed/equivalent-reflexive []) left)
       same
       (reflexive left)))
(defn- equivalent-to-at-least [left right same]
  ;; Transport the left endpoint of left<=left.  The result is right<=left,
  ;; giving the reverse direction without a separate symmetry theorem.
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left right left left
       same
       (app (function/const* 'signed/equivalent-reflexive []) left)
       (reflexive left)))
(defn- min-left [left right]
  (app (function/const* 'signed/min-lower-left []) left right))
(defn- min-right [left right]
  (app (function/const* 'signed/min-lower-right []) left right))
(defn- max-left [left right]
  (app (function/const* 'signed/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- below-min [lower left right lower-left lower-right]
  (app (function/const* 'signed/at-most-min [])
       lower left right lower-left lower-right))
(defn- max-below [left right upper left-upper right-upper]
  (app (function/const* 'signed/at-most-max [])
       left right upper left-upper right-upper))

(def clamp-spec
  {:name 'signed/clamp :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed signed)
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]]
    (minimum (maximum 'lower 'value) 'upper))})

(def clamp-lower-spec
  {:name 'signed/clamp-lower :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]]
    (at-most 'lower (clamp 'lower 'upper 'value)))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]]
    (below-min
     'lower (maximum 'lower 'value) 'upper
     (max-left 'lower 'value) 'ordered))})

(def clamp-upper-spec
  {:name 'signed/clamp-upper :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['value signed]]
    (at-most (clamp 'lower 'upper 'value) 'upper))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]]
    (min-right (maximum 'lower 'value) 'upper))})

(def clamp-in-band-spec
  {:name 'signed/clamp-in-band :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['value signed]
     ['above-lower (at-most 'lower 'value)]
     ['below-upper (at-most 'value 'upper)]]
    (equivalent (clamp 'lower 'upper 'value) 'value))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]
     ['above-lower (at-most 'lower 'value)]
     ['below-upper (at-most 'value 'upper)]]
    (let [raised (maximum 'lower 'value)
          projected (clamp 'lower 'upper 'value)
          raised<=value
          (max-below 'lower 'value 'value
                     'above-lower (reflexive 'value))
          projected<=value
          (transitive projected raised 'value
                      (min-left raised 'upper) raised<=value)
          value<=projected
          (below-min 'value raised 'upper
                     (max-right 'lower 'value) 'below-upper)]
      (antisymmetric projected 'value
                     projected<=value value<=projected)))})

(def clamp-monotone-spec
  {:name 'signed/clamp-monotone :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['left signed] ['right signed]
     ['ordered (at-most 'left 'right)]]
    (at-most (clamp 'lower 'upper 'left)
             (clamp 'lower 'upper 'right)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['left signed] ['right signed]
     ['ordered (at-most 'left 'right)]]
    (app (function/const* 'signed/min-monotone [])
         (maximum 'lower 'left) 'upper
         (maximum 'lower 'right) 'upper
         (app (function/const* 'signed/max-monotone [])
              'lower 'left 'lower 'right
              (reflexive 'lower) 'ordered)
         (reflexive 'upper)))})

(def clamp-respects-equivalence-spec
  {:name 'signed/clamp-respects-equivalence :universes []
   :type
   (function/forall
    [['lower signed] ['lower-prime signed]
     ['upper signed] ['upper-prime signed]
     ['value signed] ['value-prime signed]
     ['lower-same (equivalent 'lower 'lower-prime)]
     ['upper-same (equivalent 'upper 'upper-prime)]
     ['value-same (equivalent 'value 'value-prime)]]
    (equivalent (clamp 'lower 'upper 'value)
                (clamp 'lower-prime 'upper-prime 'value-prime)))
   :value
   (function/lam
    [['lower signed] ['lower-prime signed]
     ['upper signed] ['upper-prime signed]
     ['value signed] ['value-prime signed]
     ['lower-same (equivalent 'lower 'lower-prime)]
     ['upper-same (equivalent 'upper 'upper-prime)]
     ['value-same (equivalent 'value 'value-prime)]]
    (let [left (clamp 'lower 'upper 'value)
          right (clamp 'lower-prime 'upper-prime 'value-prime)
          lower-forward
          (equivalent-to-at-most 'lower 'lower-prime 'lower-same)
          upper-forward
          (equivalent-to-at-most 'upper 'upper-prime 'upper-same)
          value-forward
          (equivalent-to-at-most 'value 'value-prime 'value-same)
          raised-forward
          (app (function/const* 'signed/max-monotone [])
               'lower 'value 'lower-prime 'value-prime
               lower-forward value-forward)
          forward
          (app (function/const* 'signed/min-monotone [])
               (maximum 'lower 'value) 'upper
               (maximum 'lower-prime 'value-prime) 'upper-prime
               raised-forward upper-forward)
          lower-backward
          (equivalent-to-at-least 'lower 'lower-prime 'lower-same)
          upper-backward
          (equivalent-to-at-least 'upper 'upper-prime 'upper-same)
          value-backward
          (equivalent-to-at-least 'value 'value-prime 'value-same)
          raised-backward
          (app (function/const* 'signed/max-monotone [])
               'lower-prime 'value-prime 'lower 'value
               lower-backward value-backward)
          backward
          (app (function/const* 'signed/min-monotone [])
               (maximum 'lower-prime 'value-prime) 'upper-prime
               (maximum 'lower 'value) 'upper
               raised-backward upper-backward)]
      (antisymmetric left right forward backward)))})

(def clamp-below-spec
  {:name 'signed/clamp-below :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]
     ['below (at-most 'value 'lower)]]
    (equivalent (clamp 'lower 'upper 'value) 'lower))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]
     ['below (at-most 'value 'lower)]]
    (let [raised (maximum 'lower 'value)
          projected (clamp 'lower 'upper 'value)
          raised<=lower
          (max-below 'lower 'value 'lower
                     (reflexive 'lower) 'below)
          projected<=lower
          (transitive projected raised 'lower
                      (min-left raised 'upper) raised<=lower)
          lower<=projected
          (below-min 'lower raised 'upper
                     (max-left 'lower 'value) 'ordered)]
      (antisymmetric projected 'lower
                     projected<=lower lower<=projected)))})

(def clamp-above-spec
  {:name 'signed/clamp-above :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]
     ['above (at-most 'upper 'value)]]
    (equivalent (clamp 'lower 'upper 'value) 'upper))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['value signed]
     ['ordered (at-most 'lower 'upper)]
     ['above (at-most 'upper 'value)]]
    (let [raised (maximum 'lower 'value)
          projected (clamp 'lower 'upper 'value)
          upper<=raised
          (transitive 'upper 'value raised
                      'above (max-right 'lower 'value))
          upper<=projected
          (below-min 'upper raised 'upper
                     upper<=raised (reflexive 'upper))]
      (antisymmetric projected 'upper
                     (min-right raised 'upper) upper<=projected)))})

(def definition-specs [clamp-spec])
(def theorem-specs
  [clamp-lower-spec clamp-upper-spec clamp-in-band-spec
   clamp-monotone-spec clamp-respects-equivalence-spec
   clamp-below-spec clamp-above-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.minmax-algebra])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-clamp (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.clamp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
