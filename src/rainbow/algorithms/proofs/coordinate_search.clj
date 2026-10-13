(ns rainbow.algorithms.proofs.coordinate-search
  "Cyclic coordinate search over signed-rational pair state. A cycle optimizes
  along each coordinate in turn: it descends the first coordinate, then descends
  the second coordinate of the *already-updated* state, so the coordinate updates
  compose sequentially (the MAP-OVER / reduce-over-dimensions pattern, AHoF O32).
  Each coordinate update is a one-dimensional gradient step; the two partial
  gradients are parameters.

  Scope (measured by the kernel): this module has 4 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.coordinate-search`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))
(def partial-gradient-type (function/arrow state nnrat))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-subtract [left right]
  (function/app (function/const* 'signed/subtract []) left right))
(defn- first-coordinate [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- second-coordinate [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))
(defn- state-pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x y))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- descend [coordinate rate gradient s]
  (signed-subtract coordinate
                   (from-nnrat (nnrat-multiply rate (function/app gradient s)))))

(defn- update-first [rate gradient s]
  (function/app (function/const* 'search/coordinate-update-first [])
                rate gradient s))
(defn- update-second [rate gradient s]
  (function/app (function/const* 'search/coordinate-update-second [])
                rate gradient s))
(defn- cycle-of [rate gradient-first gradient-second s]
  (function/app (function/const* 'search/coordinate-cycle [])
                rate gradient-first gradient-second s))
(defn- cycle-iterate [rate gradient-first gradient-second steps initial]
  (function/app (function/const* 'search/coordinate-iterate [])
                rate gradient-first gradient-second steps initial))

;; Definitions --------------------------------------------------------------

(def update-first-spec
  {:name 'search/coordinate-update-first :kind :definition :universes []
   :type (function/forall [['rate nnrat] ['gradient partial-gradient-type]
                           ['s state]]
                          state)
   :value (function/lam [['rate nnrat] ['gradient partial-gradient-type]
                         ['s state]]
                        (state-pair
                         (descend (first-coordinate 's) 'rate 'gradient 's)
                         (second-coordinate 's)))})

(def update-second-spec
  {:name 'search/coordinate-update-second :kind :definition :universes []
   :type (function/forall [['rate nnrat] ['gradient partial-gradient-type]
                           ['s state]]
                          state)
   :value (function/lam [['rate nnrat] ['gradient partial-gradient-type]
                         ['s state]]
                        (state-pair
                         (first-coordinate 's)
                         (descend (second-coordinate 's) 'rate 'gradient 's)))})

(def cycle-spec
  {:name 'search/coordinate-cycle :kind :definition :universes []
   :type (function/forall [['rate nnrat]
                           ['gradient-first partial-gradient-type]
                           ['gradient-second partial-gradient-type]
                           ['s state]]
                          state)
   :value (function/lam [['rate nnrat]
                         ['gradient-first partial-gradient-type]
                         ['gradient-second partial-gradient-type]
                         ['s state]]
                        (update-second 'rate 'gradient-second
                                       (update-first 'rate 'gradient-first
                                                     's)))})

(def cycle-iterate-spec
  {:name 'search/coordinate-iterate :kind :definition :universes []
   :type (function/forall [['rate nnrat]
                           ['gradient-first partial-gradient-type]
                           ['gradient-second partial-gradient-type]]
                          (function/arrow nat state state))
   :value (function/lam [['rate nnrat]
                         ['gradient-first partial-gradient-type]
                         ['gradient-second partial-gradient-type]
                         ['steps nat] ['initial state]]
                        (function/app
                         (function/const* 'data/Nat.rec [type-level])
                         (function/lam [['ignored nat]] state)
                         'initial
                         (function/lam
                          [['step-index nat] ['previous state]]
                          (cycle-of 'rate 'gradient-first 'gradient-second
                                 'previous))
                         'steps))})

(def definition-specs
  [update-first-spec update-second-spec cycle-spec cycle-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def update-first-unfold-spec
  {:name 'search/coordinate-update-first-unfold :universes []
   :type (function/forall [['rate nnrat] ['gradient partial-gradient-type]
                           ['s state]]
                          (equality state
                                    (update-first 'rate 'gradient 's)
                                    (state-pair
                                     (descend (first-coordinate 's) 'rate
                                              'gradient 's)
                                     (second-coordinate 's))))
   :value (function/lam [['rate nnrat] ['gradient partial-gradient-type]
                         ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (update-first 'rate 'gradient 's)))})

(def update-second-unfold-spec
  {:name 'search/coordinate-update-second-unfold :universes []
   :type (function/forall [['rate nnrat] ['gradient partial-gradient-type]
                           ['s state]]
                          (equality state
                                    (update-second 'rate 'gradient 's)
                                    (state-pair
                                     (first-coordinate 's)
                                     (descend (second-coordinate 's) 'rate
                                              'gradient 's))))
   :value (function/lam [['rate nnrat] ['gradient partial-gradient-type]
                         ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (update-second 'rate 'gradient 's)))})

;; A cycle descends the first coordinate, then the second of that result.
(def cycle-unfold-spec
  {:name 'search/coordinate-cycle-unfold :universes []
   :type (function/forall [['rate nnrat]
                           ['gradient-first partial-gradient-type]
                           ['gradient-second partial-gradient-type]
                           ['s state]]
                          (equality state
                                    (cycle-of 'rate 'gradient-first
                                           'gradient-second 's)
                                    (update-second
                                     'rate 'gradient-second
                                     (update-first 'rate 'gradient-first 's))))
   :value (function/lam [['rate nnrat]
                         ['gradient-first partial-gradient-type]
                         ['gradient-second partial-gradient-type]
                         ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (cycle-of 'rate 'gradient-first 'gradient-second
                                      's)))})

(def cycle-iterate-zero-spec
  {:name 'search/coordinate-iterate-zero :universes []
   :type (function/forall [['rate nnrat]
                           ['gradient-first partial-gradient-type]
                           ['gradient-second partial-gradient-type]
                           ['initial state]]
                          (equality state
                                    (cycle-iterate 'rate 'gradient-first
                                                   'gradient-second
                                                   (function/const*
                                                    'data/zero [])
                                                   'initial)
                                    'initial))
   :value (function/lam [['rate nnrat]
                         ['gradient-first partial-gradient-type]
                         ['gradient-second partial-gradient-type]
                         ['initial state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state 'initial))})

(def theorem-specs
  [update-first-unfold-spec update-second-unfold-spec cycle-unfold-spec
   cycle-iterate-zero-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Coordinate-search expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :coordinate-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Coordinate-search declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.coordinate-search))
(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
