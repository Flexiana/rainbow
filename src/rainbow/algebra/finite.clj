(ns rainbow.algebra.finite
  "Exact Nat addition, finite List summation, and their first algebraic laws."
  (:require
            [rainbow.data.list :as list-data]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(def type-level list-data/type-level)
(def nat (list-data/constant-form 'data/Nat []))
(def zero (list-data/constant-form 'data/zero []))
(def successor (list-data/constant-form 'data/succ []))
(def list-nat (list-data/list-of type-level nat))
(def nil-nat (list-data/nil-of type-level nat))
(def add (list-data/constant-form 'algebra/nat-add []))
(def finite-sum (list-data/constant-form 'algebra/finite-sum []))
(def equality (list-data/constant-form 'equality/Eq [type-level]))

(defn app [function & arguments]
  (into [:app function] arguments))

(defn forall [bindings body]
  [:forall (vec bindings) body])

(defn lambda [bindings body]
  [:fn (vec bindings) body])

(defn eq [left right]
  (app equality nat left right))

(def definition-specs
  [{:name 'algebra/nat-add
    :type (forall [['left nat] ['right nat]] nat)
    :value
    (lambda [['left nat] ['right nat]]
            (app (list-data/constant-form 'data/Nat.rec [type-level])
                 (lambda [['ignored nat]] nat)
                 'right
                 (lambda [['predecessor nat] ['induction-hypothesis nat]]
                         (app successor 'induction-hypothesis))
                 'left))}

   {:name 'algebra/finite-sum
    :type (forall [['values list-nat]] nat)
    :value
    (lambda [['values list-nat]]
            (app (list-data/constant-form 'data/List.rec
                                          [type-level type-level])
                 nat
                 (lambda [['ignored list-nat]] nat)
                 zero
                 (lambda [['head nat]
                          ['tail list-nat]
                          ['induction-hypothesis nat]]
                         (app add 'head 'induction-hypothesis))
                 'values))}])

(defn base-environment []
  (let [result (persistence/load-environment "artifacts/day13/environment.edn")]
    (when-not (= :replayed (:status result))
      (throw (ex-info "Day-13 environment failed replay" {:result result})))
    (:environment result)))

(defn elaborate! [environment surface]
  (let [result (elaborate/core-expression environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite algebra expression failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn add-definition [environment {:keys [name type value]}]
  (let [core-type (elaborate! environment type)
        core-value (elaborate! environment value)
        result
        (kernel/add-declaration
         environment
         {:rainbow/kind :definition
          :rainbow/aliases #{name}
          :rainbow/universes []
          :rainbow/type core-type
          :rainbow/value core-value
          :rainbow/transparency :reducible
          :rainbow/dependencies (into (term/constants core-type)
                                      (term/constants core-value))
          :rainbow/provenance {:origin :native
                               :producer :day-14-finite-algebra
                               :arithmetic :unbounded-exact-naturals}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite algebra definition rejected"
                      {:name name :result result})))
    (:environment result)))

(defn build-definitions []
  (reduce add-definition (base-environment) definition-specs))

(defn theorem-specs []
  (let [append (list-data/constant-form 'list/append [type-level])
        map-list (list-data/constant-form 'list/map [type-level type-level])
        cons-nat (list-data/constant-form 'data/cons [type-level])]
    [{:name 'algebra/nat-add-zero-left
      :plan :reflexive
      :intros 1
      :target (forall [['right nat]] (eq (app add zero 'right) 'right))}
     {:name 'algebra/nat-add-successor-left
      :plan :reflexive
      :intros 2
      :target (forall [['left nat] ['right nat]]
                      (eq (app add (app successor 'left) 'right)
                          (app successor (app add 'left 'right))))}
     {:name 'algebra/nat-add-zero-right
      :plan :nat-zero-right
      :target (forall [['left nat]] (eq (app add 'left zero) 'left))}
     {:name 'algebra/nat-add-successor-right
      :plan :nat-successor-right
      :target (forall [['left nat] ['right nat]]
                      (eq (app add 'left (app successor 'right))
                          (app successor (app add 'left 'right))))}
     {:name 'algebra/nat-add-associative
      :plan :nat-associative
      :target (forall [['left nat] ['middle nat] ['right nat]]
                      (eq (app add (app add 'left 'middle) 'right)
                          (app add 'left (app add 'middle 'right))))}
     {:name 'algebra/finite-sum-nil
      :plan :reflexive
      :intros 0
      :target (eq (app finite-sum nil-nat) zero)}
     {:name 'algebra/finite-sum-cons
      :plan :reflexive
      :intros 2
      :target (forall [['head nat] ['tail list-nat]]
                      (eq (app finite-sum (app cons-nat nat 'head 'tail))
                          (app add 'head (app finite-sum 'tail))))}
     {:name 'algebra/finite-sum-zero-cons
      :plan :reflexive
      :intros 1
      :target (forall [['tail list-nat]]
                      (eq (app finite-sum
                               (app cons-nat nat zero 'tail))
                          (app finite-sum 'tail)))}
     {:name 'algebra/finite-sum-singleton
      :plan :finite-sum-singleton
      :target (forall [['value nat]]
                      (eq (app finite-sum
                               (app cons-nat nat 'value nil-nat))
                          'value))}
     {:name 'algebra/finite-sum-zero
      :plan :finite-sum-zero
      :target (forall [['values list-nat]]
                      (eq (app finite-sum
                               (app map-list nat nat
                                    (lambda [['ignored nat]] zero)
                                    'values))
                          zero))}
     {:name 'algebra/finite-sum-append-additive
      :plan :finite-sum-append
      :target (forall [['left list-nat] ['right list-nat]]
                      (eq (app finite-sum (app append nat 'left 'right))
                          (app add (app finite-sum 'left)
                               (app finite-sum 'right))))}]))

(defn run-tactics! [environment target tactics]
  (reduce
   (fn [result next-tactic]
     (when-not (or (:state result) (= :proved (:status result)))
       (throw (ex-info "Tactic plan lost its proof state" {:result result})))
     (when (= :proved (:status result))
       (throw (ex-info "Tactic plan continued after completing the proof"
                       {:result result})))
     (let [next-result (tactic/run (:state result) next-tactic)]
       (when (= :failure (:status next-result))
         (throw (ex-info "Finite algebra tactic failed"
                         {:failure (:failure next-result)})))
       next-result))
   (proof/start environment target)
   tactics))

(defn named-level-application [environment alias levels & arguments]
  (reduce term/application
          (term/constant (environment/resolve-id environment alias) levels)
          arguments))

(defn named-application [environment alias & arguments]
  (apply named-level-application environment alias [] arguments))

(defn core-finite-sum [environment value]
  (named-application environment 'algebra/finite-sum value))

(defn finite-sum-append-step-proof
  "Builds the cons case from congruence, associativity, symmetry, and
  transitivity. Context is [IH tail head right left]."
  [environment]
  (let [nat-term (named-application environment 'data/Nat)
        head (term/bound 2)
        tail (term/bound 1)
        right (term/bound 3)
        hypothesis (term/bound 0)
        append-tail (named-level-application environment 'list/append
                                               [type-level]
                                               nat-term tail right)
        sum-append-tail (core-finite-sum environment append-tail)
        sum-tail (core-finite-sum environment tail)
        sum-right (core-finite-sum environment right)
        summed-tail-right (named-application environment 'algebra/nat-add
                                              sum-tail sum-right)
        add-head (term/lambda-term
                  nat-term
                  (named-application environment 'algebra/nat-add
                                     (term/shift head 1) (term/bound 0)))
        lifted
        (named-level-application environment 'equality/congruent-function
                                 [type-level type-level]
                                 nat-term nat-term add-head
                                 sum-append-tail summed-tail-right hypothesis)
        left-associated
        (named-application environment 'algebra/nat-add
                           (named-application environment 'algebra/nat-add
                                              head sum-tail)
                           sum-right)
        right-associated
        (named-application environment 'algebra/nat-add head summed-tail-right)
        associative
        (named-application environment 'algebra/nat-add-associative
                           head sum-tail sum-right)
        reversed-associative
        (named-level-application environment 'equality/symmetric [type-level]
                                 nat-term left-associated right-associated
                                 associative)
        original-left
        (named-application environment 'algebra/nat-add head sum-append-tail)]
    (named-level-application environment 'equality/transitive [type-level]
                             nat-term original-left right-associated left-associated
                             lifted reversed-associative)))

(defn proof-plan [environment plan intro-count]
  (case plan
    :reflexive
    (concat (repeat intro-count (tactic/intro))
            [(tactic/reflexivity)])

    :nat-zero-right
    [(tactic/intro 'left)
     (tactic/induction (term/bound 0))
     (tactic/reflexivity)
     (tactic/intro 'predecessor)
     (tactic/intro 'induction-hypothesis)
     ;; Rewriting the successor result from right to left avoids rewriting the
     ;; recursive expression inside its own induction evidence.
     (tactic/rewrite (term/bound 0) {:direction :backward})
     (tactic/reflexivity)]

    :nat-successor-right
    [(tactic/intro 'left)
     (tactic/intro 'right)
     (tactic/induction (term/bound 1))
     (tactic/reflexivity)
     (tactic/intro 'predecessor)
     (tactic/intro 'induction-hypothesis)
     (tactic/rewrite (term/bound 0) {:direction :backward})
     (tactic/reflexivity)]

    :nat-associative
    [(tactic/intro 'left)
     (tactic/intro 'middle)
     (tactic/intro 'right)
     (tactic/induction (term/bound 2))
     (tactic/reflexivity)
     (tactic/intro 'predecessor)
     (tactic/intro 'induction-hypothesis)
     (tactic/rewrite (term/bound 0) {:direction :backward})
     (tactic/reflexivity)]

    :finite-sum-zero
    [(tactic/intro 'values)
     (tactic/induction (term/bound 0))
     (tactic/reflexivity)
     (tactic/intro 'head)
     (tactic/intro 'tail)
     (tactic/intro 'induction-hypothesis)
     ;; The cons case reduces to the induction hypothesis because 0 + n is
     ;; computational for this exact Nat addition.
     (tactic/exact (term/bound 0))]

    :finite-sum-singleton
    [(tactic/intro 'value)
     (tactic/exact
      (named-application environment 'algebra/nat-add-zero-right
                         (term/bound 0)))]

    :finite-sum-append
    [(tactic/intro 'left)
     (tactic/intro 'right)
     (tactic/induction (term/bound 1))
     (tactic/reflexivity)
     (tactic/intro 'head)
     (tactic/intro 'tail)
     (tactic/intro 'induction-hypothesis)
     (tactic/exact (finite-sum-append-step-proof environment))]))

(defn prove-theorem [environment {:keys [target plan intros]}]
  (let [core-target (elaborate! environment target)]
    (run-tactics! environment core-target
                  (proof-plan environment plan (or intros 0)))))

(defn register-theorem [environment spec]
  (let [result (prove-theorem environment spec)]
    (when-not (= :proved (:status result))
      (throw (ex-info "Finite algebra proof did not finish"
                      {:name (:name spec) :result result})))
    (let [type (get-in result [:proof :proof/type])
          value (get-in result [:proof :proof/term])
          added
          (kernel/add-declaration
           environment
           {:rainbow/kind :theorem
            :rainbow/aliases #{(:name spec)}
            :rainbow/universes []
            :rainbow/type type
            :rainbow/value value
            :rainbow/transparency :opaque
            :rainbow/dependencies (into (term/constants type)
                                        (term/constants value))
            :rainbow/provenance {:origin :native
                                 :producer :day-14-finite-algebra
                                 :assurance :kernel-checked-exact}
            :rainbow/schema-version 1})]
      (when-not (= :accepted (:status added))
        (throw (ex-info "Finite algebra theorem declaration rejected"
                        {:name (:name spec) :result added})))
      {:environment (:environment added)
       :result result
       :declaration (:declaration added)
       :name (:name spec)
       :plan (:plan spec)})))

(defn build []
  (reduce
   (fn [{:keys [environment results]} spec]
     (let [registered (register-theorem environment spec)]
       {:environment (:environment registered)
        :results (conj results (dissoc registered :environment))}))
   {:environment (build-definitions) :results []}
   (theorem-specs)))






