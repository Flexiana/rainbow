(ns rainbow.render
  "A human-readable VIEW of a kernel statement, laid out like a function signature.

  What the kernel checks is the term, not this text. The renderer reads a checked
  declaration's type and prints it with alias names instead of content hashes,
  binder names where they can be recovered, decimal numerals, infix arithmetic and
  order, sums, maxima and bounded quantifiers, and lists as data. Every notation it
  uses is listed in a legend naming the constant behind it; a long application that
  repeats is abbreviated by a `where` line that spells it out; anything cut by the
  depth budget is an explicit elision `…⟨n⟩` counting the term nodes left out.

  Binder names are not part of a kernel term (binders are de Bruijn indices). When
  the theorem's source spec is loaded, its statement is elaborated again and its
  names are used only if the result is EXACTLY the kernel's type; otherwise names
  are generated. Nothing here is trusted, and nothing here changes what is checked."
  (:require [clojure.string :as string]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]))

;; ---------------------------------------------------------------- binder names from the source spec

(defn- spec-candidates [x]
  (cond (and (map? x) (symbol? (:name x)) (contains? x :type)) [x]
        (and (sequential? x) (seq x) (every? map? x)) (filter #(and (symbol? (:name %)) (contains? % :type)) x)
        :else []))

(defn- loaded-specs [alias]
  (for [ns (all-ns)
        v (vals (ns-publics ns))
        :when (and (bound? v) (not (fn? @v)))
        spec (try (doall (spec-candidates @v)) (catch Throwable _ []))
        :when (= alias (:name spec))]
    spec))

(defn- annotate
  "The kernel term with binder names from the surface form it was elaborated from:
  [:pi d b mode name] / [:lam d b mode name]. Shapes that do not line up keep no name."
  [surface term]
  (let [tag (when (vector? surface) (first surface))]
    (cond
      (and (#{:forall :fn} tag) (= 3 (count surface)) (seq (second surface))
           (= (if (= tag :forall) :pi :lam) (first term)))
      (let [[[name domain] & more] (second surface)
            rest-surface (if (seq more) [tag (vec more) (nth surface 2)] (nth surface 2))]
        [(first term) (annotate domain (nth term 1)) (annotate rest-surface (nth term 2)) (nth term 3) name])

      (and (= :-> tag) (>= (count surface) 3) (= :pi (first term)))
      (let [[_ domain & more] surface
            rest-surface (if (= 1 (count more)) (first more) (into [:->] more))]
        [:pi (annotate domain (nth term 1)) (annotate rest-surface (nth term 2)) (nth term 3) nil])

      (and (= :app tag) (>= (count surface) 3))
      (let [[_ f & args] surface
            spine (loop [t term n (count args) acc ()]
                    (cond (zero? n) [t acc]
                          (= :app (first t)) (recur (nth t 1) (dec n) (cons (nth t 2) acc))))]
        (if-let [[head targs] spine]
          (reduce (fn [acc [s t]] [:app acc (annotate s t)]) (annotate f head) (map vector args targs))
          term))

      (and (= :let tag) (= 5 (count surface)) (= :let (first term)))
      (let [[_ _ ty value body] surface]
        [:let (annotate ty (nth term 1)) (annotate value (nth term 2)) (annotate body (nth term 3))])

      :else term)))

(defn- strip [t]
  (case (first t)
    (:pi :lam) [(first t) (strip (nth t 1)) (strip (nth t 2)) (nth t 3)]
    :app [:app (strip (nth t 1)) (strip (nth t 2))]
    :let [:let (strip (nth t 1)) (strip (nth t 2)) (strip (nth t 3))]
    t))

(defn named-type
  "The declaration's type annotated with source binder names, or nil when no loaded
  spec elaborates to exactly this type."
  [env alias type]
  (some (fn [spec]
          (let [r (elaborate/core-expression env (:type spec))]
            (when (and (= :elaborated (:status r)) (= type (:term r)))
              (let [named (annotate (:type spec) type)]
                (when (= type (strip named)) named)))))
        (loaded-specs alias)))

;; ---------------------------------------------------------------- notation

(def ^:private notation
  "alias -> how it prints. Every entry used in a rendering is listed in its legend."
  {'signed/at-most {:infix "≤" :arity 2 :prec 50} 'nnrat/at-most {:infix "≤" :arity 2 :prec 50}
   'nat/at-most {:infix "≤" :arity 2 :prec 50} 'signed/less-than {:infix "<" :arity 2 :prec 50}
   'signed/equivalent {:infix "=" :arity 2 :prec 50 :note "signed/equivalent: equality of rational values"}
   'nnrat/equivalent {:infix "=" :arity 2 :prec 50 :note "nnrat/equivalent: equality of rational values"}
   'equality/Eq {:infix "=" :arity 3 :prec 50 :drop 1 :note "equality/Eq"}
   'signed/add {:infix "+" :arity 2 :prec 65} 'nnrat/add {:infix "+" :arity 2 :prec 65}
   'signed/subtract {:infix "-" :arity 2 :prec 65}
   'signed/multiply {:infix "·" :arity 2 :prec 70} 'nnrat/multiply {:infix "·" :arity 2 :prec 70}
   'signed/SignedRational {:symbol "ℚ"} 'nnrat/NonnegativeRational {:symbol "ℚ≥0"} 'data/Nat {:symbol "ℕ"}
   'signed/zero {:symbol "0"} 'signed/one {:symbol "1"} 'nnrat/zero {:symbol "0"} 'nnrat/one {:symbol "1"}
   'data/List {:symbol "List"} 'finset-data/Finset {:symbol "Finset"}
   'signed/map-sum {:special :sum :arity 3 :symbol "Σ" :note "signed/map-sum: sum over the listed indices"}
   'signed/all-at-most {:special :all-at-most :arity 4 :symbol "∀ i ∈ xs, f i ≤ g i"
                        :note "signed/all-at-most: the bound at every listed index"}
   'finset-data/to-set {:special :member :arity 3 :symbol "∈" :note "finset-data/to-set: membership in a finite set"}
   'metric/finite-nnrat-sup-radius {:special :sup-distance :arity 4 :symbol "max s∈S |f s - g s|"
                                    :note "metric/finite-nnrat-sup-radius: largest distance over the listed states (0 if none)"}})

(def ^:private prop-heads
  '#{signed/at-most nnrat/at-most nat/at-most signed/less-than signed/equivalent nnrat/equivalent
     equality/Eq signed/all-at-most finset-data/to-set})

;; ---------------------------------------------------------------- term helpers

(defn- spine [t]
  (loop [t t args ()] (if (= :app (first t)) (recur (nth t 1) (cons (nth t 2) args)) [t (vec args)])))

(defn- subscript [n] (apply str (map #(char (+ 0x2080 (- (int %) 48))) (str n))))

(defn- node-count [t] (count (filter #(and (vector? %) (keyword? (first %))) (tree-seq vector? seq t))))

(defn- free-indices
  "The de Bruijn indices free in t, relative to t's own position."
  ([t] (free-indices t 0))
  ([t depth]
   (case (first t)
     :bound (if (>= (second t) depth) #{(- (second t) depth)} #{})
     (:sort :const) #{}
     :app (into (free-indices (nth t 1) depth) (free-indices (nth t 2) depth))
     (:pi :lam) (into (free-indices (nth t 1) depth) (free-indices (nth t 2) (inc depth)))
     :let (into (into (free-indices (nth t 1) depth) (free-indices (nth t 2) depth)) (free-indices (nth t 3) (inc depth)))
     #{})))

(defn- uses-bound-zero? [body] (contains? (free-indices body) 0))

;; ---------------------------------------------------------------- printing

(defn- renderer
  "Printing state for one statement. `abbreviations` maps a rendered application prefix
  to the name it is printed as; `candidates` collects prefixes that could be abbreviated."
  [env {:keys [max-depth] :or {max-depth 14}} abbreviations]
  (let [aliases (reduce-kv (fn [m alias id]
                             (update m id #(if (and % (<= (count (str %)) (count (str alias)))) % alias)))
                           {} (:rainbow.environment/aliases env))
        id->notation (into {} (keep (fn [[alias n]] (when-let [id (environment/resolve-id env alias)]
                                                      [id (assoc n :alias alias)])))
                           notation)
        legend (atom (sorted-map)) elided (atom 0) counters (atom {}) candidates (atom {})
        top (volatile! 0)]
    (letfn [(alias-of [id] (or (aliases id) (str "#" (subs id 7 15))))
            (note! [n] (swap! legend assoc (or (:infix n) (:symbol n)) (or (:note n) (str (:alias n)))))
            (fresh [names base]
              (let [taken (set names)]
                (if-not (taken base) base
                        (loop [k 1] (let [c (str base (subscript k))] (if (taken c) (recur (inc k)) c))))))
            (prop-like? [t]
              (let [t (loop [t t] (if (= :pi (first t)) (recur (nth t 2)) t))
                    [h] (spine t)]
                (and (= :const (first h)) (contains? prop-heads (aliases (second h))))))
            (binder-name [names domain body given]
              (if (and given (or (nil? body) (uses-bound-zero? body)))
                (fresh names (str given))
                (let [base (if (prop-like? domain) "h" "x")]
                  (fresh names (str base (subscript (get (swap! counters update base (fnil inc 0)) base)))))))
            (numeral [t]
              (loop [t t n 0]
                (let [[h args] (spine t) a (when (= :const (first h)) (aliases (second h)))]
                  (cond (and (= 'data/zero a) (empty? args)) n
                        (and (= 'data/succ a) (= 1 (count args))) (recur (first args) (inc n))))))
            (rational [t]
              (let [[h args] (spine t) a (when (= :const (first h)) (aliases (second h)))]
                (case a
                  nnrat/make (let [[n d] (map numeral args)] (when (and n d (= 2 (count args))) (/ n (inc d))))
                  signed/make (let [[p q] (map rational args)] (when (and p q (= 2 (count args))) (- p q)))
                  nil)))
            (list-items [t]
              (loop [t t items []]
                (let [[h args] (spine t) a (when (= :const (first h)) (aliases (second h)))]
                  (cond (and (= 'data/nil a) (= 1 (count args))) items
                        (and (= 'data/cons a) (= 3 (count args))) (recur (nth args 2) (conj items (nth args 1)))))))
            (paren [s inner outer] (if (< inner outer) (str "(" s ")") s))
            (level [l] (cond (= l [:zero]) 0
                             (= (first l) :succ) (let [x (level (second l))] (if (number? x) (inc x) (str x "+1")))
                             (= (first l) :param) (str (second l))
                             :else (pr-str l)))
            (sort-name [l] (cond (= l [:zero]) "Prop" (= l [:succ [:zero]]) "Type"
                                 (= (first l) :succ) (str "Type " (level (second l)))
                                 :else (str "Sort " (level l))))
            (at [f names d nm]
              ;; f applied to the bound name nm, beta-reduced when f is a lambda
              (if (= :lam (first f))
                (show (nth f 2) (cons nm names) d 51)
                (str (show f names d 100) " " nm)))
            (lam-name [names fs default]
              (fresh names (or (some #(when (and (= :lam (first %)) (get % 4) (uses-bound-zero? (nth % 2))) (str (get % 4))) fs)
                               default)))
            (rec-items [body idx depth]
              ;; Nat.rec M v0 (fun p _ => Nat.rec M v1 (...) p) idx as [[v0 depth] [v1 depth+2] ...]: the
              ;; entries of a lookup table, each with the number of binders it sits under (it must not use them).
              ;; idx :any accepts any index at the outer level.
              (loop [body body idx idx depth depth items []]
                (let [[h args] (spine body)]
                  (if (and (= :const (first h)) (= 'data/Nat.rec (aliases (second h))) (= 4 (count args))
                           (or (= :any idx) (= idx (nth args 3))))
                    (let [[_ v step] args]
                      (when (and (not-any? #(< % depth) (free-indices v))
                                 (= :lam (first step)) (= :lam (first (nth step 2))))
                        (recur (nth (nth step 2) 2) [:bound 1] (+ depth 2) (conj items [v depth]))))
                    (when (and (seq items) (not-any? #(< % depth) (free-indices body)))
                      (conj items [body depth]))))))
            (table-items [t]
              (when (and (= :lam (first t)) (= :const (first (nth t 1))) (= 'data/Nat (aliases (second (nth t 1)))))
                (rec-items (nth t 2) [:bound 0] 1)))
            (show-items [items names d]
              (note! {:symbol "[a, b, …]" :note "data/Nat.rec lookup table: entry k at index k; the last entry also at every later index"})
              (str "[" (string/join ", " (map (fn [[v k]] (show v (concat (repeat k "_") names) d 0)) items)) "]"))
            (show [t names depth prec]
              (if (> depth max-depth)
                (let [n (node-count t)] (swap! elided + n) (str "…⟨" n "⟩"))
                (let [d (inc depth)]
                  (case (first t)
                    :sort (sort-name (second t))
                    :bound (nth names (second t) (str "?" (second t)))
                    :const (if (numeral t) "0" (if-let [n (id->notation (second t))]
                             (if (and (:symbol n) (not (:special n))) (do (note! n) (:symbol n)) (str (:alias n)))
                             (alias-of (second t))))
                    :lam (if-let [items (table-items t)]
                           (show-items items names d)
                         (let [nm (binder-name names (nth t 1) (nth t 2) (get t 4))]
                           (paren (str "fun " nm " => " (show (nth t 2) (cons nm names) d 0)) 0 prec)))
                    :let (let [nm (fresh names "v")]
                           (paren (str "let " nm " := " (show (nth t 2) names d 0) "; "
                                       (show (nth t 3) (cons nm names) d 0)) 0 prec))
                    :pi (if (and (nil? (get t 4)) (not (uses-bound-zero? (nth t 2))))
                          (paren (str (show (nth t 1) names d 26) " → " (show (nth t 2) (cons "_" names) d 25)) 25 prec)
                          (let [nm (binder-name names (nth t 1) nil (get t 4))]
                            (paren (str "∀ (" nm " : " (show (nth t 1) names d 0) "), "
                                        (show (nth t 2) (cons nm names) d 0)) 0 prec)))
                    :app (show-app t names d prec)))))
            (hoistable? [t names]
              ;; mentions only signature parameters, so it means the same wherever it appears
              (let [locals (- (count names) @top)]
                (every? #(>= % locals) (free-indices t))))
            (show-app [t names d prec]
              (if-let [r (or (numeral t) (rational t))]
                (if (ratio? r) (str (numerator r) "/" (denominator r)) (str r))
                (if-let [items (list-items t)]
                  (str "[" (string/join ", " (map #(show % names d 0) items)) "]")
                 (if-let [inline (and (= :app (first t)) (= 4 (count (second (spine t)))) (rec-items t :any 0))]
                  (str (show-items inline names d) "[" (show (nth (second (spine t)) 3) names d 0) "]")
                 (if (and (= :app (first t)) (table-items (first (spine t))))
                  (apply str (show (first (spine t)) names d 100) (map #(str "[" (show % names d 0) "]") (second (spine t))))
                  (let [[h args] (spine t)
                        n (when (= :const (first h)) (id->notation (second h)))]
                    (cond
                      (and (:infix n) (= (:arity n) (count args)))
                      (let [[a b] (drop (or (:drop n) 0) args) p (:prec n)]
                        (note! n)
                        (paren (str (show a names d (if (= p 50) 51 p)) " " (:infix n) " " (show b names d (inc p))) p prec))

                      (and (= :sum (:special n)) (= 3 (count args)))
                      (let [[_ f xs] args nm (lam-name names [f] "j")]
                        (note! n)
                        (paren (str "Σ " nm "∈" (show xs names d 100) ", " (at f names d nm)) 66 prec))

                      (and (= :all-at-most (:special n)) (= 4 (count args)))
                      (let [[_ f g xs] args nm (lam-name names [f g] "i")]
                        (note! n)
                        (paren (str "∀ " nm " ∈ " (show xs names d 100) ", " (at f names d nm) " ≤ " (at g names d nm)) 0 prec))

                      (and (= :member (:special n)) (= 3 (count args)))
                      (let [[_ s e] args]
                        (note! n)
                        (paren (str (show e names d 51) " ∈ " (show s names d 51)) 50 prec))

                      (and (= :sup-distance (:special n)) (= 4 (count args)))
                      (let [[_ source f g] args nm (lam-name names [f g] "s")]
                        (note! n)
                        (paren (str "max " nm "∈" (show source names d 100) " |" (at f names d nm) " - " (at g names d nm) "|") 66 prec))

                      :else
                      (let [prefix (fn [k] (reduce (fn [acc a] [:app acc a]) h (take k args)))
                            hit (when (= :const (first h))
                                  (some (fn [k]
                                          (let [p (prefix k)]
                                            (when (hoistable? p names)
                                              (let [s (string/join " " (cons (show h names d 100) (map #(show % names d 101) (take k args))))]
                                                (swap! candidates update s (fnil inc 0))
                                                (when-let [nm (abbreviations s)] [nm k])))))
                                        (range (count args) 1 -1)))]
                        (when n (note! n))
                        (if-let [[nm k] hit]
                          (paren (string/join " " (cons nm (map #(show % names d 101) (drop k args)))) 100 prec)
                          (paren (string/join " " (cons (show h names d 100) (map #(show % names d 101) args))) 100 prec))))))))))]
      {:show show :legend legend :elided elided :binder-name binder-name :prop-like? prop-like?
       :candidates candidates :top top})))

(defn- layout [env decl type opts abbreviations]
  (let [{:keys [show legend elided binder-name prop-like? candidates top]} (renderer env opts abbreviations)
        [params concl]
        (loop [t type names () params []]
          (if (= :pi (first t))
            (let [nm (binder-name names (nth t 1) nil (get t 4))]
              (vreset! top (count names))
              (let [ty (show (nth t 1) names 0 0)]
                (recur (nth t 2) (cons nm names) (conj params {:name nm :type ty :hypothesis? (prop-like? (nth t 1))}))))
            (do (vreset! top (count names)) [params (show t names 0 0)])))]
    {:params params :concl concl :legend @legend :elided @elided :candidates @candidates}))

(declare declaration-statement)

(defn statement
  "The statement of a checked declaration, laid out like a signature. Returns
  {:text :names :elided :legend}."
  ([env id-or-alias] (statement env id-or-alias {}))
  ([env id-or-alias opts]
   (let [id (environment/resolve-id env id-or-alias)
         decl (environment/declaration env id)]
     (declaration-statement env decl (if (symbol? id-or-alias) id-or-alias (first (sort (:rainbow/aliases decl)))) opts))))

(defn declaration-statement
  "Like statement, for a declaration given as data (for example one read from a proof
  bundle before it is checked). Its constants must resolve in env."
  ([env decl alias] (declaration-statement env decl alias {}))
  ([env decl alias {:keys [width] :or {width 88} :as opts}]
   (let [
         named (named-type env alias (:rainbow/type decl))
         type (or named (:rainbow/type decl))
         first-pass (layout env decl type opts {})
         abbreviations (->> (:candidates first-pass)
                            (filter (fn [[s n]] (and (>= n 2) (>= (count s) 40))))
                            (sort-by (comp - count key))
                            (reduce (fn [m [s _]]
                                      (if (some #(string/includes? % s) (keys m)) m
                                          (let [base (-> s (string/split #" ") first (string/split #"/") last
                                                         (string/split #"-") last)
                                                taken (set (vals m))
                                                nm (if (taken base) (str base (subscript (count m))) base)]
                                            (assoc m s nm))))
                                    {}))
         {:keys [params concl legend elided]} (layout env decl type opts abbreviations)
         groups (reduce (fn [acc {:keys [name type hypothesis?]}]
                          (let [{pnames :names pty :type ph :hypothesis?} (peek acc)]
                            (if (and pty (not hypothesis?) (not ph) (= pty type))
                              (conj (pop acc) {:names (conj pnames name) :type type :hypothesis? false})
                              (conj acc {:names [name] :type type :hypothesis? hypothesis?}))))
                        [] params)
         binder (fn [{:keys [names type]}] (str "(" (string/join " " names) " : " type ")"))
         lines (mapv first
                      (reduce (fn [lines g]
                                (let [b (binder g) [last-line data?] (peek lines)]
                                  (if (and (not (:hypothesis? g)) data?
                                           (<= (+ (count last-line) 1 (count b)) width))
                                    (conj (pop lines) [(str last-line " " b) true])
                                    (conj lines [(str "  " b) (not (:hypothesis? g))]))))
                              [] groups))
         header (str alias (when (seq (:rainbow/universes decl))
                             (str ".{" (string/join ", " (:rainbow/universes decl)) "}")) " :")
         wheres (for [[s nm] (sort-by val abbreviations)] (str "  where " nm " := " s))]
     {:text (string/join "\n" (concat [header] lines [(str "  → " concl)] wheres))
      :names (if named :source :generated)
      :elided elided
      :legend legend})))

(defn print-statement [env id-or-alias & [opts]]
  (let [{:keys [text names elided legend]} (statement env id-or-alias opts)]
    (println text)
    (println (str "  -- binder names: " (name names)
                  (when (pos? elided) (str "; " elided " term nodes elided as …⟨n⟩"))))
    (doseq [[sym meaning] legend] (println (str "  -- " sym "  " meaning)))))
