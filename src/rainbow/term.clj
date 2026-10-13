(ns rainbow.term
  "Canonical V0 core terms and capture-avoiding binder operations."
  (:require [rainbow.canonical :as canonical]))

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
       (case (first level)
         :zero (= 1 (count level))
         :succ (and (= 2 (count level)) (level? (second level)))
         :max (and (= 3 (count level)) (level? (second level)) (level? (nth level 2)))
         :imax (and (= 3 (count level)) (level? (second level)) (level? (nth level 2)))
         :param (and (= 2 (count level)) (symbol? (second level)))
         false)))

(defn normalize-level [level]
  (case (first level)
    :zero zero-level
    :param level
    :succ [:succ (normalize-level (second level))]
    :max (let [left (normalize-level (second level))
               right (normalize-level (nth level 2))]
           (cond
             (= left zero-level) right
             (= right zero-level) left
             (= left right) left
             (and (= :succ (first left)) (= :succ (first right)))
             [:succ (normalize-level [:max (second left) (second right)])]
             (pos? (compare (canonical/encode left) (canonical/encode right))) [:max right left]
             :else [:max left right]))
    :imax (let [left (normalize-level (second level))
                right (normalize-level (nth level 2))]
            (cond
              (= right zero-level) zero-level
              (= left zero-level) right
              (= left right) left
              (= :succ (first right)) (normalize-level [:max left right])
              :else [:imax left right]))))

(defn level-params [level]
  (case (first level)
    :zero #{}
    :param #{(second level)}
    :succ (level-params (second level))
    (:max :imax) (into (level-params (second level))
                       (level-params (nth level 2)))))

(defn instantiate-level [level substitution]
  (normalize-level
   (case (first level)
     :zero level
     :param (get substitution (second level) level)
     :succ [:succ (instantiate-level (second level) substitution)]
     :max [:max (instantiate-level (second level) substitution)
           (instantiate-level (nth level 2) substitution)]
     :imax [:imax (instantiate-level (second level) substitution)
            (instantiate-level (nth level 2) substitution)])))

(defn term? [term]
  (and (vector? term)
       (case (first term)
         :sort (and (= 2 (count term)) (level? (second term)))
         :bound (and (= 2 (count term))
                     (integer? (second term))
                     (not (neg? (second term))))
         :const (and (= 3 (count term))
                     (string? (second term))
                     (.startsWith ^String (second term) "sha256:")
                     (vector? (nth term 2))
                     (every? level? (nth term 2)))
         :app (and (= 3 (count term)) (term? (second term)) (term? (nth term 2)))
         (:lam :pi) (and (= 4 (count term))
                         (term? (second term))
                         (term? (nth term 2))
                         (contains? #{:explicit :implicit} (nth term 3)))
         :let (and (= 4 (count term))
                   (term? (second term))
                   (term? (nth term 2))
                   (term? (nth term 3)))
         false)))

(defn assert-term! [term]
  (when-not (term? term)
    (throw (ex-info "Malformed core term"
                    {:error/category :term/malformed
                     :term term})))
  term)

(defn shift
  "Shifts free de Bruijn indices >= cutoff by delta."
  ([term delta] (shift term delta 0))
  ([term delta cutoff]
   (letfn [(walk [node depth]
             (case (first node)
               :sort node
               :bound (let [index (second node)]
                        (if (>= index (+ cutoff depth))
                          (let [shifted (+ index delta)]
                            (when (neg? shifted)
                              (throw (ex-info "de Bruijn shift escaped its scope"
                                              {:error/category :term/invalid-shift
                                               :index index :delta delta :cutoff cutoff})))
                            [:bound shifted])
                          node))
               :const node
               :app [:app (walk (second node) depth) (walk (nth node 2) depth)]
               :lam [:lam (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
               :pi [:pi (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
               :let [:let (walk (second node) depth)
                     (walk (nth node 2) depth)
                     (walk (nth node 3) (inc depth))]))]
     (walk term 0))))

(defn instantiate
  "Substitutes argument for bound 0 in body and removes that binder."
  [body argument]
  (letfn [(walk [node depth]
            (case (first node)
              :sort node
              :bound (let [index (second node)]
                       (cond
                         (= index depth) (shift argument depth)
                         (> index depth) [:bound (dec index)]
                         :else node))
              :const node
              :app [:app (walk (second node) depth) (walk (nth node 2) depth)]
              :lam [:lam (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :pi [:pi (walk (second node) depth) (walk (nth node 2) (inc depth)) (nth node 3)]
              :let [:let (walk (second node) depth)
                    (walk (nth node 2) depth)
                    (walk (nth node 3) (inc depth))]))]
    (walk body 0)))

(defn instantiate-universes [term substitution]
  (case (first term)
    :sort [:sort (instantiate-level (second term) substitution)]
    :bound term
    :const [:const (second term) (mapv #(instantiate-level % substitution) (nth term 2))]
    :app [:app (instantiate-universes (second term) substitution)
          (instantiate-universes (nth term 2) substitution)]
    :lam [:lam (instantiate-universes (second term) substitution)
          (instantiate-universes (nth term 2) substitution)
          (nth term 3)]
    :pi [:pi (instantiate-universes (second term) substitution)
         (instantiate-universes (nth term 2) substitution)
         (nth term 3)]
    :let [:let (instantiate-universes (second term) substitution)
          (instantiate-universes (nth term 2) substitution)
          (instantiate-universes (nth term 3) substitution)]))

(defn constants [term]
  (case (first term)
    (:sort :bound) #{}
    :const #{(second term)}
    :app (into (constants (second term)) (constants (nth term 2)))
    (:lam :pi) (into (constants (second term)) (constants (nth term 2)))
    :let (into (constants (second term))
               (into (constants (nth term 2)) (constants (nth term 3))))))

(defn closed? [term]
  (letfn [(walk [node depth]
            (case (first node)
              :bound (< (second node) depth)
              (:sort :const) true
              :app (and (walk (second node) depth) (walk (nth node 2) depth))
              (:lam :pi) (and (walk (second node) depth) (walk (nth node 2) (inc depth)))
              :let (and (walk (second node) depth)
                        (walk (nth node 2) depth)
                        (walk (nth node 3) (inc depth)))))]
    (walk term 0)))

(defn pretty [term]
  (case (first term)
    :sort (str "Sort(" (pr-str (normalize-level (second term))) ")")
    :bound (str "#" (second term))
    :const (str "@" (second term))
    :app (str "(" (pretty (second term)) " " (pretty (nth term 2)) ")")
    :lam (str "(fn [_:" (pretty (second term)) "] " (pretty (nth term 2)) ")")
    :pi (str "(Pi [_:" (pretty (second term)) "] " (pretty (nth term 2)) ")")
    :let (str "(let [_:" (pretty (second term)) " " (pretty (nth term 2)) "] "
              (pretty (nth term 3)) ")")))
