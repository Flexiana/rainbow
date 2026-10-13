(ns rainbow.math.rational.nnrat.farkas-elim-two-var
  "Constructive composition of list-sized elimination for two decoupled nnrat
  variables.

  Each variable has its own list of lower bounds and non-empty family of upper
  bounds.  The original system nests witnesses for v and w; the reduced system
  is the conjunction of the two one-variable reductions.  The proofs explicitly
  compose farkas-elim-list extension and projection in both directions.  There
  are no coupling constraints in this bounded milestone.  Native and axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- variable-satisfies [lowers u0 urest value]
  (proposition/conjunction (ge-all lowers value) (le-all u0 urest value)))
(defn- list-reduced [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-reduced [])
                lowers u0 urest))
(defn- list-solvable [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-solvable [])
                lowers u0 urest))
(defn- system [lowers-v u0v urest-v lowers-w u0w urest-w v w]
  (function/app (function/const* 'nnrat/farkas-elim-two-var-system [])
                lowers-v u0v urest-v lowers-w u0w urest-w v w))
(defn- reduced [lowers-v u0v urest-v lowers-w u0w urest-w]
  (function/app (function/const* 'nnrat/farkas-elim-two-var-reduced [])
                lowers-v u0v urest-v lowers-w u0w urest-w))
(defn- solvable [lowers-v u0v urest-v lowers-w u0w urest-w]
  (function/app (function/const* 'nnrat/farkas-elim-two-var-solvable [])
                lowers-v u0v urest-v lowers-w u0w urest-w))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- witness [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat predicate value evidence))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nnrat predicate result evidence continue))

(def system-spec
  {:name 'nnrat/farkas-elim-two-var-system :kind :definition :universes []
   :type (function/arrow
          list-nnrat nnrat list-nnrat list-nnrat nnrat list-nnrat
          nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]
     ['v nnrat] ['w nnrat]]
    (proposition/conjunction
     (variable-satisfies 'lowers-v 'u0v 'urest-v 'v)
     (variable-satisfies 'lowers-w 'u0w 'urest-w 'w)))})

(def reduced-spec
  {:name 'nnrat/farkas-elim-two-var-reduced :kind :definition :universes []
   :type (function/arrow
          list-nnrat nnrat list-nnrat list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]]
    (proposition/conjunction
     (list-reduced 'lowers-v 'u0v 'urest-v)
     (list-reduced 'lowers-w 'u0w 'urest-w)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-two-var-solvable :kind :definition :universes []
   :type (function/arrow
          list-nnrat nnrat list-nnrat list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['v nnrat]]
      (proposition/existence
       type-level nnrat
       (function/lam
        [['w nnrat]]
        (system 'lowers-v 'u0v 'urest-v
                'lowers-w 'u0w 'urest-w 'v 'w))))))})

(def definition-specs [system-spec reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-two-var-extends :universes []
   :type
   (function/forall
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]
     ['reduced-feasible
      (reduced 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)]]
    (solvable 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w))
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]
     ['reduced-feasible
      (reduced 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)]]
    (let [reduced-v (list-reduced 'lowers-v 'u0v 'urest-v)
          reduced-w (list-reduced 'lowers-w 'u0w 'urest-w)
          feasible-v (left-conjunct reduced-v reduced-w 'reduced-feasible)
          feasible-w (right-conjunct reduced-v reduced-w 'reduced-feasible)
          predicate-v
          (function/lam
           [['candidate nnrat]]
           (variable-satisfies 'lowers-v 'u0v 'urest-v 'candidate))
          predicate-w
          (function/lam
           [['candidate nnrat]]
           (variable-satisfies 'lowers-w 'u0w 'urest-w 'candidate))
          solution-v
          (function/app (function/const* 'nnrat/farkas-elim-list-extends [])
                        'lowers-v 'u0v 'urest-v feasible-v)
          solution-w
          (function/app (function/const* 'nnrat/farkas-elim-list-extends [])
                        'lowers-w 'u0w 'urest-w feasible-w)
          result (solvable 'lowers-v 'u0v 'urest-v
                           'lowers-w 'u0w 'urest-w)
          outer-predicate
          (function/lam
           [['v nnrat]]
           (proposition/existence
            type-level nnrat
            (function/lam
             [['w nnrat]]
             (system 'lowers-v 'u0v 'urest-v
                     'lowers-w 'u0w 'urest-w 'v 'w))))]
      (use-witness
       predicate-v result solution-v
       (function/lam
        [['v nnrat]
         ['satisfies-v
          (variable-satisfies 'lowers-v 'u0v 'urest-v 'v)]]
        (let [inner-predicate
              (function/lam
               [['w nnrat]]
               (system 'lowers-v 'u0v 'urest-v
                       'lowers-w 'u0w 'urest-w 'v 'w))]
          (use-witness
           predicate-w result solution-w
           (function/lam
            [['w nnrat]
             ['satisfies-w
              (variable-satisfies 'lowers-w 'u0w 'urest-w 'w)]]
            (let [satisfies-system
                  (conjoin
                   (variable-satisfies 'lowers-v 'u0v 'urest-v 'v)
                   (variable-satisfies 'lowers-w 'u0w 'urest-w 'w)
                   'satisfies-v 'satisfies-w)
                  inner-solution
                  (witness inner-predicate 'w satisfies-system)]
              (witness outer-predicate 'v inner-solution)))))))))})

(def projects-spec
  {:name 'nnrat/farkas-elim-two-var-projects :universes []
   :type
   (function/forall
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]
     ['solution
      (solvable 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)]]
    (reduced 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w))
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]
     ['solution
      (solvable 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)]]
    (let [result (reduced 'lowers-v 'u0v 'urest-v
                          'lowers-w 'u0w 'urest-w)
          outer-predicate
          (function/lam
           [['v nnrat]]
           (proposition/existence
            type-level nnrat
            (function/lam
             [['w nnrat]]
             (system 'lowers-v 'u0v 'urest-v
                     'lowers-w 'u0w 'urest-w 'v 'w))))]
      (use-witness
       outer-predicate result 'solution
       (function/lam
        [['v nnrat]
         ['inner-solution
          (proposition/existence
           type-level nnrat
           (function/lam
            [['w nnrat]]
            (system 'lowers-v 'u0v 'urest-v
                    'lowers-w 'u0w 'urest-w 'v 'w)))]]
        (let [inner-predicate
              (function/lam
               [['w nnrat]]
               (system 'lowers-v 'u0v 'urest-v
                       'lowers-w 'u0w 'urest-w 'v 'w))]
          (use-witness
           inner-predicate result 'inner-solution
           (function/lam
            [['w nnrat]
             ['satisfies
              (system 'lowers-v 'u0v 'urest-v
                      'lowers-w 'u0w 'urest-w 'v 'w)]]
            (let [satisfies-v-prop
                  (variable-satisfies 'lowers-v 'u0v 'urest-v 'v)
                  satisfies-w-prop
                  (variable-satisfies 'lowers-w 'u0w 'urest-w 'w)
                  satisfies-v
                  (left-conjunct satisfies-v-prop satisfies-w-prop 'satisfies)
                  satisfies-w
                  (right-conjunct satisfies-v-prop satisfies-w-prop 'satisfies)
                  predicate-v
                  (function/lam
                   [['candidate nnrat]]
                   (variable-satisfies
                    'lowers-v 'u0v 'urest-v 'candidate))
                  predicate-w
                  (function/lam
                   [['candidate nnrat]]
                   (variable-satisfies
                    'lowers-w 'u0w 'urest-w 'candidate))
                  solution-v (witness predicate-v 'v satisfies-v)
                  solution-w (witness predicate-w 'w satisfies-w)
                  reduced-v
                  (function/app
                   (function/const* 'nnrat/farkas-elim-list-projects [])
                   'lowers-v 'u0v 'urest-v solution-v)
                  reduced-w
                  (function/app
                   (function/const* 'nnrat/farkas-elim-list-projects [])
                   'lowers-w 'u0w 'urest-w solution-w)]
              (conjoin
               (list-reduced 'lowers-v 'u0v 'urest-v)
               (list-reduced 'lowers-w 'u0w 'urest-w)
               reduced-v reduced-w)))))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-two-var-solvable-iff :universes []
   :type
   (function/forall
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]]
    (proposition/equivalence
     (reduced 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)
     (solvable 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)))
   :value
   (function/lam
    [['lowers-v list-nnrat] ['u0v nnrat] ['urest-v list-nnrat]
     ['lowers-w list-nnrat] ['u0w nnrat] ['urest-w list-nnrat]]
    (let [reduced-prop
          (reduced 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)
          solvable-prop
          (solvable 'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-two-var-extends [])
         'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w
         'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-two-var-projects [])
         'lowers-v 'u0v 'urest-v 'lowers-w 'u0w 'urest-w
         'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-two-var (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-two-var))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
