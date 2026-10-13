(ns rainbow.math.logic.classical
  "Reusable classical theorems derived as proof data from explicit profiles."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(defn- app [function & arguments]
  (apply proposition/app function arguments))

(defn- const* [name]
  (proposition/const* name []))

(defn- excluded-middle [claim]
  (app (const* 'logic/excluded-middle) claim))

(defn- use-disjunction [left right result evidence on-left on-right]
  (app (const* 'proposition/use-disjunction)
       left right result evidence on-left on-right))

(defn- explode [result impossible]
  (app (const* 'proposition/explode) result impossible))

(def theorem-specs
  [{:name 'logic/classical-double-negation-elimination
    :universes []
    :type
    (proposition/forall
     [['claim 'Prop :implicit]
      ['not-not-claim
       (proposition/negation (proposition/negation 'claim))]]
     'claim)
    :value
    (proposition/lam
     [['claim 'Prop :implicit]
      ['not-not-claim
       (proposition/negation (proposition/negation 'claim))]]
     (use-disjunction
      'claim (proposition/negation 'claim) 'claim
      (excluded-middle 'claim)
      (proposition/lam [['claim-evidence 'claim]] 'claim-evidence)
      (proposition/lam
       [['not-claim (proposition/negation 'claim)]]
       (explode 'claim (app 'not-not-claim 'not-claim)))))}

   {:name 'logic/classical-cases
    :universes []
    :type
    (proposition/forall
     [['claim 'Prop :implicit] ['result 'Prop :implicit]
      ['when-claim (proposition/arrow 'claim 'result)]
      ['when-not-claim
       (proposition/arrow (proposition/negation 'claim) 'result)]]
     'result)
    :value
    (proposition/lam
     [['claim 'Prop :implicit] ['result 'Prop :implicit]
      ['when-claim (proposition/arrow 'claim 'result)]
      ['when-not-claim
       (proposition/arrow (proposition/negation 'claim) 'result)]]
     (use-disjunction
      'claim (proposition/negation 'claim) 'result
      (excluded-middle 'claim) 'when-claim 'when-not-claim))}

   {:name 'logic/classical-swapped-excluded-middle
    :universes []
    :type
    (proposition/forall
     [['claim 'Prop]]
     (proposition/disjunction (proposition/negation 'claim) 'claim))
    :value
    (proposition/lam
     [['claim 'Prop]]
     (use-disjunction
      'claim (proposition/negation 'claim)
      (proposition/disjunction (proposition/negation 'claim) 'claim)
      (excluded-middle 'claim)
      (proposition/lam
       [['claim-evidence 'claim]]
       (app (const* 'proposition/right-disjunct)
            (proposition/negation 'claim) 'claim 'claim-evidence))
      (proposition/lam
       [['not-claim (proposition/negation 'claim)]]
       (app (const* 'proposition/left-disjunct)
            (proposition/negation 'claim) 'claim 'not-claim))))}

   {:name 'logic/classical-peirce
    :universes []
    :type
    (proposition/forall
     [['claim 'Prop] ['result 'Prop]
      ['continue
       (proposition/arrow (proposition/arrow 'claim 'result) 'claim)]]
     'claim)
    :value
    (proposition/lam
     [['claim 'Prop] ['result 'Prop]
      ['continue
       (proposition/arrow (proposition/arrow 'claim 'result) 'claim)]]
     (app
      (const* 'logic/classical-double-negation-elimination)
      'claim
      (proposition/lam
       [['not-claim (proposition/negation 'claim)]]
       (app
        'not-claim
        (app
         'continue
         (proposition/lam
          [['claim-evidence 'claim]]
          (explode 'result (app 'not-claim 'claim-evidence))))))))}])

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Classical proof data failed elaboration"
                      {:error/category :classical/elaboration-failed
                       :surface surface :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native
           :producer :classical-proof-data
           :logical/profile :classical}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Classical theorem was kernel rejected"
                      {:error/category :classical/kernel-rejected
                       :theorem (:name spec) :result result})))
    [(:environment result) (:declaration result)]))

(defn extend-activation
  "Adds ordinary classical theorem proofs after a profile containing excluded
  middle has been activated."
  [activation]
  (when-not (contains? (:logical/principles activation) :classical)
    (throw (ex-info "Classical derivations require the classical profile"
                    {:error/category :classical/missing-profile
                     :logical/profile (:logical/profile activation)})))
  (let [[checked-environment declarations]
        (reduce
         (fn [[environment declarations] spec]
           (let [[next-environment declaration] (add-spec environment spec)]
             [next-environment (conj declarations declaration)]))
         [(:environment activation) []]
         theorem-specs)]
    {:status :extended
     :activation activation
     :environment checked-environment
     :declarations declarations
     :trusted-kernel-change :none}))
