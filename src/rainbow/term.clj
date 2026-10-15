(ns rainbow.term
  "Canonical V0 core terms and capture-avoiding binder operations."
  (:require [rainbow.canonical :as canonical]))

;; first/second without allocating a seq (terms and levels are vectors)
(defmacro ^:private fst [x] `(nth ~x 0 nil))
(defmacro ^:private snd [x] `(nth ~x 1 nil))

(def zero-level [:zero])

(defn sort-term [level] [:sort level])
(defn bound [index] [:bound index])
(defn constant
  ([id] (constant id []))
  ([id levels] [:const id (vec levels)]))
(defn application [function argument] [:app function argument])
(defn lambda-term
  ([binder-type body] (lambda-term binder-type body :explicit))
  ([binder-type body mode] [:lam binder-type body mode]))
(defn pi-term
  ([binder-type body] (pi-term binder-type body :explicit))
  ([binder-type body mode] [:pi binder-type body mode]))
(defn let-term [type value body] [:let type value body])

(defn level? [level]
  (and (vector? level)
       (case (fst level)
         :zero (= 1 (count level))
         :succ (and (= 2 (count level)) (level? (snd level)))
         :max (and (= 3 (count level)) (level? (snd level)) (level? (nth level 2)))
         :imax (and (= 3 (count level)) (level? (snd level)) (level? (nth level 2)))
         :param (and (= 2 (count level)) (symbol? (snd level)))
         false)))

(defn normalize-level [level]
  (case (fst level)
    :zero zero-level
    :param level
    :succ [:succ (normalize-level (snd level))]
    :max (let [left (normalize-level (snd level))
               right (normalize-level (nth level 2))]
           (cond
             (= left zero-level) right
             (= right zero-level) left
             (= left right) left
             (and (= :succ (fst left)) (= :succ (fst right)))
             [:succ (normalize-level [:max (snd left) (snd right)])]
             (pos? (compare (canonical/encode left) (canonical/encode right))) [:max right left]
             :else [:max left right]))
    :imax (let [left (normalize-level (snd level))
                right (normalize-level (nth level 2))]
            (cond
              (= right zero-level) zero-level
              (= left zero-level) right
              (= left right) left
              (= :succ (fst right)) (normalize-level [:max left right])
              :else [:imax left right]))))

(defn level-params [level]
  (case (fst level)
    :zero #{}
    :param #{(snd level)}
    :succ (level-params (snd level))
    (:max :imax) (into (level-params (snd level))
                       (level-params (nth level 2)))))

(defn instantiate-level [level substitution]
  (normalize-level
   (case (fst level)
     :zero level
     :param (get substitution (snd level) level)
     :succ [:succ (instantiate-level (snd level) substitution)]
     :max [:max (instantiate-level (snd level) substitution)
           (instantiate-level (nth level 2) substitution)]
     :imax [:imax (instantiate-level (snd level) substitution)
            (instantiate-level (nth level 2) substitution)])))

(defn term? [term]
  (and (vector? term)
       (case (fst term)
         :sort (and (= 2 (count term)) (level? (snd term)))
         :bound (and (= 2 (count term))
                     (integer? (snd term))
                     (not (neg? (snd term))))
         ;; a natural-number literal: [:nat n] denotes data/succ applied n times to data/zero
         :nat (and (= 2 (count term))
                   (integer? (snd term))
                   (not (neg? (snd term))))
         :const (and (= 3 (count term))
                     (string? (snd term))
                     (.startsWith ^String (snd term) "sha256:")
                     (vector? (nth term 2))
                     (every? level? (nth term 2)))
         :app (and (= 3 (count term)) (term? (snd term)) (term? (nth term 2)))
         (:lam :pi) (and (= 4 (count term))
                         (term? (snd term))
                         (term? (nth term 2))
                         (contains? #{:explicit :implicit} (nth term 3)))
         :let (and (= 4 (count term))
                   (term? (snd term))
                   (term? (nth term 2))
                   (term? (nth term 3)))
         false)))

(defn assert-term! [term]
  (when-not (term? term)
    (throw (ex-info "Malformed core term"
                    {:error/category :term/malformed
                     :term term})))
  term)

(def ^:private ranges
  ;; loose ranges by term identity, per thread; emptied when large. A range is a
  ;; function of the term alone, so dropping entries never changes a result.
  (ThreadLocal/withInitial (reify java.util.function.Supplier (get [_] (java.util.IdentityHashMap.)))))

(defn loose-range
  "One more than the largest de Bruijn index free in term (0 when it is closed).
  Substitution leaves a subterm whose range does not reach the
  substituted index untouched instead of rebuilding it."
  [term]
  (case (fst term)
    (:sort :const :nat) 0
    :bound (inc' (snd term))
    (let [^java.util.IdentityHashMap cache (.get ^ThreadLocal ranges)]
      (when (> (.size cache) 1000000) (.clear cache))
      (if-let [cached (.get cache term)]
        cached
        (let [under #(max 0 (dec (loose-range %)))
              range (case (fst term)
                      :app (max (loose-range (snd term)) (loose-range (nth term 2)))
                      (:lam :pi) (max (loose-range (snd term)) (under (nth term 2)))
                      :let (max (loose-range (snd term)) (loose-range (nth term 2)) (under (nth term 3))))]
          (.put cache term range)
          range)))))

(defn shift
  "Shifts free de Bruijn indices >= cutoff by delta."
  ([term delta] (shift term delta 0))
  ([term delta cutoff]
   (letfn [(walk [node depth]
             (if (<= (loose-range node) (+ cutoff depth))
               node
             (case (fst node)
               (:sort :nat) node
               :bound (let [index (snd node)]
                        (if (>= index (+ cutoff depth))
                          (let [shifted (+ index delta)]
                            (when (neg? shifted)
                              (throw (ex-info "de Bruijn shift escaped its scope"
                                              {:error/category :term/invalid-shift
                                               :index index :delta delta :cutoff cutoff})))
                            [:bound shifted])
                          node))
               :const node
               :app [:app (walk (snd node) depth) (walk (nth node 2) depth)]
               :lam [:lam (walk (snd node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
               :pi [:pi (walk (snd node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
               :let [:let (walk (snd node) depth)
                     (walk (nth node 2) depth)
                     (walk (nth node 3) (inc depth))])))]
     (walk term 0))))

(defn instantiate
  "Substitutes argument for bound 0 in body and removes that binder."
  [body argument]
  (let [closed? (zero? (loose-range argument))]
  (letfn [(walk [node depth]
            (if (<= (loose-range node) depth)
              node
            (case (fst node)
              (:sort :nat) node
              :bound (let [index (snd node)]
                       (cond
                         (= index depth) (if closed? argument (shift argument depth))
                         (> index depth) [:bound (dec index)]
                         :else node))
              :const node
              :app [:app (walk (snd node) depth) (walk (nth node 2) depth)]
              :lam [:lam (walk (snd node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :pi [:pi (walk (snd node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :let [:let (walk (snd node) depth)
                    (walk (nth node 2) depth)
                    (walk (nth node 3) (inc depth))])))]
    (walk body 0))))

(declare instantiate-universes)

(def ^:private level-normalized
  ;; definition bodies unfolded without universe arguments, by identity, per thread:
  ;; the same body is unfolded many times and its levels need normalizing once
  (ThreadLocal/withInitial (reify java.util.function.Supplier (get [_] (java.util.IdentityHashMap.)))))

(defn- universes-normalized [term]
  (let [^java.util.IdentityHashMap cache (.get ^ThreadLocal level-normalized)]
    (when (> (.size cache) 100000) (.clear cache))
    (or (.get cache term)
        ;; a non-empty map that substitutes nothing: the levels are only normalized,
        ;; exactly as unfolding with no universe arguments always did
        (let [result (instantiate-universes term {::none true})]
          (.put cache term result)
          result))))

(defn instantiate-universes [term substitution]
  (if (empty? substitution)
    (universes-normalized term)
  (case (fst term)
    :sort [:sort (instantiate-level (snd term) substitution)]
    (:bound :nat) term
    :const [:const (snd term) (mapv #(instantiate-level % substitution) (nth term 2))]
    :app [:app (instantiate-universes (snd term) substitution)
          (instantiate-universes (nth term 2) substitution)]
    :lam [:lam (instantiate-universes (snd term) substitution)
          (instantiate-universes (nth term 2) substitution)
          (nth term 3)]
    :pi [:pi (instantiate-universes (snd term) substitution)
         (instantiate-universes (nth term 2) substitution)
         (nth term 3)]
    :let [:let (instantiate-universes (snd term) substitution)
          (instantiate-universes (nth term 2) substitution)
          (instantiate-universes (nth term 3) substitution)])))

(defn constants [term]
  (case (fst term)
    (:sort :bound :nat) #{}
    :const #{(snd term)}
    :app (into (constants (snd term)) (constants (nth term 2)))
    (:lam :pi) (into (constants (snd term)) (constants (nth term 2)))
    :let (into (constants (snd term))
               (into (constants (nth term 2)) (constants (nth term 3))))))

(defn closed? [term]
  (letfn [(walk [node depth]
            (case (fst node)
              :bound (< (snd node) depth)
              (:sort :const :nat) true
              :app (and (walk (snd node) depth) (walk (nth node 2) depth))
              (:lam :pi) (and (walk (snd node) depth) (walk (nth node 2) (inc depth)))
              :let (and (walk (snd node) depth)
                        (walk (nth node 2) depth)
                        (walk (nth node 3) (inc depth)))))]
    (walk term 0)))

(defn pretty [term]
  (case (fst term)
    :sort (str "Sort(" (pr-str (normalize-level (snd term))) ")")
    :bound (str "#" (snd term))
    :const (str "@" (snd term))
    :nat (str (snd term))
    :app (str "(" (pretty (snd term)) " " (pretty (nth term 2)) ")")
    :lam (str "(fn [_:" (pretty (snd term)) "] " (pretty (nth term 2)) ")")
    :pi (str "(Pi [_:" (pretty (snd term)) "] " (pretty (nth term 2)) ")")
    :let (str "(let [_:" (pretty (snd term)) " " (pretty (nth term 2)) "] "
              (pretty (nth term 3)) ")")))
