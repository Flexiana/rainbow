(ns rainbow.foreign.mathlib-native-test
  (:require [clojure.test :refer :all]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance :as nat-distance]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib-native :as native]
            [rainbow.math.logic.proposition :as proposition]))

(def checked-environment (delay (proposition/build-environment)))

(defn statement [name universes type]
  {:rainbow.catalog/kind :statement
   :foreign/name name
   :foreign/universes universes
   :foreign/type-fingerprint (str "test:" name)
   :foreign/type type
   :foreign/value :redacted})

;; A checkpoint environment that carries both the native Nat inductive block
;; (so `data/zero` resolves) and equality -- the same accumulated environment
;; the Nat distance proofs are checked in.
(def numeral-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint nat-distance/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Nat distance checkpoint rejected"
                        {:checkpoint checkpoint})))
      (:environment checkpoint))))

;; The exact placeholder the proof-redacted exporter emits for a Nat literal,
;; and the canonical instance term that wraps it.
(def zero-literal [:unsupported :literal "Lean.Literal.natVal 0"])
(def zero-instance [:app [:const "instOfNatNat" []] zero-literal])

(defn nat-numeral
  "The frozen exporter encoding of a Nat numeral as
  `@OfNat.ofNat Nat <literal> (instOfNatNat <literal>)`."
  [literal]
  [:app
   [:app
    [:app [:const "OfNat.ofNat" [[:zero]]] [:const "Nat" []]]
    literal]
   [:app [:const "instOfNatNat" []] literal]])

(defn nat-eq-statement
  "A statement type `@Eq Nat left right` over foreign Nat encodings."
  [name left right]
  (statement name []
             [:app
              [:app
               [:app [:const "Eq" [[:succ [:zero]]]] [:const "Nat" []]]
               left]
              right]))

(deftest nativeization-preserves-universes-and-supported-binder-modes
  (let [result
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.polymorphic"
                    ["u"]
                    [:pi [:sort [:param "u"]]
                     [:pi [:bound 0] [:bound 1] :explicit]
                     :implicit]))]
    (is (= :nativeized (:status result)))
    (is (= ['u] (:universes result)))
    (is (= [:pi [:sort [:param 'u]]
            [:pi [:bound 0] [:bound 1] :explicit]
            :implicit]
           (:type result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= :sort (first (get-in result [:kernel :sort]))))))

(deftest legacy-statements-derive-universes-deterministically
  (let [result
        (native/nativeize-statement-type
         @checked-environment
         (dissoc
          (statement "Example.legacy" nil
                     [:pi [:sort [:param "z"]]
                      [:pi [:sort [:param "a"]] [:sort [:zero]] :explicit]
                      :explicit])
          :foreign/universes))]
    (is (= :nativeized (:status result)))
    (is (= ['a 'z] (:universes result)))))

(deftest logical-constants-resolve-to-native-content-identities
  (let [result
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.and"
                    []
                    [:pi [:sort [:zero]]
                     [:pi [:sort [:zero]]
                      [:app [:app [:const "And" []] [:bound 1]] [:bound 0]]
                      :implicit]
                     :implicit]))
        conjunction-id (environment/resolve-id
                        @checked-environment 'proposition/conjunction)]
    (is (= :nativeized (:status result)))
    (is (= ["And"] (:foreign/constants result)))
    (is (= conjunction-id
           (get-in result [:type 2 2 1 1 1])))))

(deftest nativeization-normalizes-instance-binders-and-rejects-unsupported-binders
  (let [unknown
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.unknown" [] [:const "Opaque.Foreign" []]))
        instance-binder
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.instance" []
                    [:pi [:sort [:zero]] [:bound 0] :instance-implicit]))
        strict-binder
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.strict" []
                    [:pi [:sort [:zero]] [:bound 0] :strict-implicit]))]
    (is (= :mathlib-native/unknown-constant
           (get-in unknown [:error :error/category])))
    (is (= :nativeized (:status instance-binder)))
    (is (= :implicit (nth (:type instance-binder) 3)))
    (is (= :mathlib-native/unsupported-binder
           (get-in strict-binder [:error :error/category])))))

(deftest nativeization-refuses-visible-foreign-proofs
  (let [result
        (native/nativeize-statement-type
         @checked-environment
         (assoc (statement "Example.visible" [] [:sort [:zero]])
                :foreign/value [:bound 0]))]
    (is (= :mathlib-native/proof-not-redacted
           (get-in result [:error :error/category])))))

(deftest iff-elimination-nativeizes-inside-a-dependent-predicate
  (let [raw
        [:pi [:sort [:zero]]
         [:pi [:sort [:zero]]
          [:pi [:pi [:bound 1] [:sort [:zero]] :explicit]
           [:pi [:pi [:bound 2] [:sort [:zero]] :explicit]
            [:pi [:pi [:bound 3]
                  [:app [:app [:const "Iff" []]
                         [:app [:bound 2] [:bound 0]]]
                   [:app [:bound 1] [:bound 0]]]
                  :explicit]
             [:pi [:app [:app [:const "Iff" []] [:bound 4]] [:bound 3]]
              [:app
               [:app
                [:app [:const "Eq" [[:succ [:zero]]]] [:sort [:zero]]]
                [:pi [:bound 5] [:app [:bound 4] [:bound 0]] :explicit]]
               [:pi [:bound 4]
                [:app [:bound 3]
                 [:app
                  [:app
                   [:app
                    [:app [:const "Iff.mpr" []] [:bound 6]]
                    [:bound 5]]
                   [:bound 1]]
                  [:bound 0]]]
                :explicit]]
              :explicit]
             :explicit]
            :explicit]
           :implicit]
          :implicit]
         :implicit]
        result
        (native/nativeize-statement-type
         @checked-environment
         (statement "Example.iff-mpr-in-predicate" [] raw))]
    (is (= :nativeized (:status result)))
    (is (= ["Eq" "Iff" "Iff.mpr"] (:foreign/constants result)))
    (is (= :checked (get-in result [:kernel :status])))))

(deftest inequality-and-unique-existence-use-native-proof-data
  (let [inequality
        (native/nativeize-statement-type
         @checked-environment
         (statement
          "Example.ne" ["u"]
          [:pi [:sort [:param "u"]]
           [:pi [:bound 0]
            [:pi [:bound 1]
             [:app [:app [:app [:const "Ne" [[:param "u"]]] [:bound 2]]
                    [:bound 1]]
              [:bound 0]]
             :explicit]
            :explicit]
           :implicit]))
        unique
        (native/nativeize-statement-type
         @checked-environment
         (statement
          "Example.exists-unique" ["u"]
          [:pi [:sort [:param "u"]]
           [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
            [:app [:app [:const "ExistsUnique" [[:param "u"]]] [:bound 1]]
             [:bound 0]]
            :explicit]
           :implicit]))]
    (is (= :nativeized (:status inequality)))
    (is (= ["Ne"] (:foreign/constants inequality)))
    (is (= :nativeized (:status unique)))
    (is (= ["ExistsUnique"] (:foreign/constants unique)))))

;; -- Narrow typed Nat-zero literal bridge ----------------------------------

(deftest frozen-nat-zero-numeral-rewrites-to-native-data-zero
  ;; The exact EDN the exporter emitted for `(0 : Nat)`.
  (let [numeral
        [:app
         [:app
          [:app [:const "OfNat.ofNat" [[:zero]]] [:const "Nat" []]]
          [:unsupported :literal "Lean.Literal.natVal 0"]]
         [:app [:const "instOfNatNat" []]
          [:unsupported :literal "Lean.Literal.natVal 0"]]]
        environment @numeral-environment
        zero-id (environment/resolve-id environment 'data/zero)
        result (native/nativeize-statement-type
                environment (nat-eq-statement "Nat.zero-eq-zero" numeral numeral))]
    (is (= :nativeized (:status result)))
    ;; Both operands of the equation became the native data/zero constructor.
    (is (= [:const zero-id []] (get-in result [:type 2])))
    (is (= [:const zero-id []] (get-in result [:type 1 2])))
    ;; The provenance fingerprint still records the foreign literal machinery.
    (is (= ["Eq" "Nat" "OfNat.ofNat" "instOfNatNat"]
           (:foreign/constants result)))
    (is (= :checked (get-in result [:kernel :status])))))

(deftest nat-zero-bridge-uses-the-shared-numeral-helper
  (let [environment @numeral-environment
        zero-id (environment/resolve-id environment 'data/zero)
        result (native/nativeize-statement-type
                environment
                (nat-eq-statement "Nat.helper-zero"
                                  (nat-numeral zero-literal)
                                  (nat-numeral zero-literal)))]
    (is (= :nativeized (:status result)))
    (is (= [:const zero-id []] (get-in result [:type 2])))))

(deftest nat-literal-bridge-rejects-nonzero-values
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.five"
                           []
                           (nat-numeral
                            [:unsupported :literal "Lean.Literal.natVal 5"])))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-value
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-unsupported-literal-kinds
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.string"
                           []
                           (nat-numeral
                            [:unsupported :literal "Lean.Literal.strVal \"x\""])))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-value
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-wrong-carrier-type
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Int.zero"
                           []
                           [:app
                            [:app
                             [:app [:const "OfNat.ofNat" [[:zero]]]
                              [:const "Int" []]]
                             zero-literal]
                            [:app [:const "instOfNatInt" []] zero-literal]]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-type
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-wrong-instance
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.bad-instance"
                           []
                           [:app
                            [:app
                             [:app [:const "OfNat.ofNat" [[:zero]]]
                              [:const "Nat" []]]
                             zero-literal]
                            [:const "Wrong.instance" []]]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-instance
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-malformed-spine
  ;; OfNat.ofNat applied to only the carrier type -- missing literal + instance.
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.partial"
                           []
                           [:app [:const "OfNat.ofNat" [[:zero]]]
                            [:const "Nat" []]]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/malformed-nat-literal
           (get-in result [:error :error/category])))))

(deftest bare-unsupported-node-is-rejected-without-a-literal-evaluator
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.bare-literal" [] zero-literal))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-mismatched-instance-payload
  ;; Value literal is 0 but the instance carries a different literal payload.
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.instance-payload-mismatch"
                           []
                           [:app
                            [:app
                             [:app [:const "OfNat.ofNat" [[:zero]]]
                              [:const "Nat" []]]
                             zero-literal]
                            [:app [:const "instOfNatNat" []]
                             [:unsupported :literal "Lean.Literal.natVal 1"]]]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-instance
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-extra-instance-application
  ;; instOfNatNat applied to an extra argument beyond the literal.
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.instance-over-applied"
                           []
                           [:app
                            [:app
                             [:app [:const "OfNat.ofNat" [[:zero]]]
                              [:const "Nat" []]]
                             zero-literal]
                            [:app
                             [:app [:const "instOfNatNat" []] zero-literal]
                             zero-literal]]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/unsupported-literal-instance
           (get-in result [:error :error/category])))))

(deftest nat-literal-bridge-rejects-wrong-ofnat-universe-levels
  ;; The OfNat.ofNat head carries a non-frozen universe level.
  (let [result (native/nativeize-statement-type
                @numeral-environment
                (statement "Nat.wrong-levels"
                           []
                           [:app
                            [:app
                             [:app [:const "OfNat.ofNat" [[:succ [:zero]]]]
                              [:const "Nat" []]]
                             zero-literal]
                            zero-instance]))]
    (is (= :rejected (:status result)))
    (is (= :mathlib-native/malformed-nat-literal
           (get-in result [:error :error/category])))))
