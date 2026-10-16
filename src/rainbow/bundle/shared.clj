(ns rainbow.bundle.shared
  "The shared encoding of a proof bundle: the same declarations, written as a DAG.

  A proof term repeats itself. The c2 LP certificate's proof has 46,325 term nodes
  but only 617 distinct ones, and it names 26 constants 21,938 times, each by a
  71-character content hash. Written as a tree, most of the file is repetition.

  This encoding writes every distinct subterm once, in a node table where a node's
  children are earlier entries named by position, and every constant once, in a
  constant table that a node names by position. Decoding rebuilds exactly the same
  terms, so the kernel checks exactly the same declarations and computes exactly
  the same content ids.

  Nothing here is trusted. The decoder refuses anything that is not well formed,
  and whatever it produces still goes through kernel/add-declaration, which
  recomputes each declaration's id from its content and rejects one that differs
  from the id the bundle states. A decoding defect therefore shows up as a refused
  bundle, never as an accepted wrong one.

  Format, as EDN:
    {:rainbow.bundle/schema-version 3            ; the shared encoding
     :rainbow.bundle/payload-schema 1 or 2       ; the plain bundle it encodes
     :constants [\"sha256:...\" ...]              ; constant table
     :terms [node ...]                           ; node table, children before parents
     ... every other key exactly as in the plain bundle, except that a
     declaration's :rainbow/type and :rainbow/value are node positions and its
     :rainbow/dependencies are constant positions}

  Nodes: [:sort level] [:bound i] [:nat n] [:const k levels] [:app f a] [:lam domain body
  mode] [:pi domain body mode] [:let type value body], where f, a, domain, body,
  type and value are positions of earlier nodes and k is a constant position.")

(def schema-version 3)

;; ---------------------------------------------------------------- encode

(defn- encoder []
  {:constants (java.util.LinkedHashMap.) :nodes (java.util.HashMap.) :table (java.util.ArrayList.)})

(defn- constant-index [{:keys [^java.util.LinkedHashMap constants]} id]
  (or (.get constants id)
      (let [k (.size constants)] (.put constants id k) k)))

(defn- term-index
  "Position of term in the node table, adding it (after its children) if new."
  [{:keys [^java.util.HashMap nodes ^java.util.ArrayList table] :as enc} term]
  (or (.get nodes term)
      (let [node (case (first term)
                   :sort term
                   :bound term
                   :nat term
                   :const [:const (constant-index enc (second term)) (nth term 2)]
                   :app [:app (term-index enc (nth term 1)) (term-index enc (nth term 2))]
                   (:lam :pi) [(first term) (term-index enc (nth term 1)) (term-index enc (nth term 2))
                               (nth term 3)]
                   :let [:let (term-index enc (nth term 1)) (term-index enc (nth term 2))
                         (term-index enc (nth term 3))]
                   (throw (ex-info "not a kernel term" {:term term})))
            i (.size table)]
        (.add table node)
        (.put nodes term i)
        i)))

(defn- encode-declaration [enc declaration]
  (cond-> declaration
    (contains? declaration :rainbow/type) (update :rainbow/type #(term-index enc %))
    (some? (:rainbow/value declaration)) (update :rainbow/value #(term-index enc %))
    (contains? declaration :rainbow/dependencies)
    (update :rainbow/dependencies #(into (sorted-set) (map (partial constant-index enc)) %))))

(defn encode
  "The shared encoding of a plain (schema 1 or 2) proof bundle."
  [bundle]
  (let [payload (:rainbow.bundle/schema-version bundle)
        _ (when-not (#{1 2} payload)
            (throw (ex-info "only schema 1 and 2 bundles can be shared" {:schema payload})))
        enc (encoder)
        encoded (case payload
                  1 (update bundle :declarations #(mapv (partial encode-declaration enc) %))
                  2 (update bundle :entries
                            #(mapv (fn [entry]
                                     (if (= :declaration (:entry/kind entry))
                                       (update entry :entry/value (partial encode-declaration enc))
                                       entry))
                                   %)))]
    (assoc encoded
           :rainbow.bundle/schema-version schema-version
           :rainbow.bundle/payload-schema payload
           :constants (vec (keys (:constants enc)))
           :terms (vec (:table enc)))))

;; ---------------------------------------------------------------- decode

(defn- refuse! [message data]
  (throw (ex-info (str "malformed shared bundle: " message) (assoc data :error/category :bundle/malformed-shared))))

(defn- position! [x limit what]
  (when-not (and (int? x) (<= 0 x) (< x limit))
    (refuse! (str what " is not a position in range") {:value x :limit limit}))
  x)

(defn- decode-terms
  "The node table as terms. Every child must name an EARLIER node, so the table is
  acyclic by construction and decodes in one pass; equal positions decode to the
  same object."
  [constants nodes]
  (when-not (vector? nodes) (refuse! ":terms must be a vector" {}))
  (let [constants (vec constants)
        n-constants (count constants)]
    (reduce
     (fn [built node]
       (let [i (count built)
             child #(nth built (position! % i (str "a child of node " i)))]
         (when-not (vector? node) (refuse! "a node must be a vector" {:node i}))
         (conj built
               (case (first node)
                 :sort (do (when-not (= 2 (count node)) (refuse! "bad :sort node" {:node i})) node)
                 :bound (do (when-not (and (= 2 (count node)) (int? (second node)))
                              (refuse! "bad :bound node" {:node i}))
                            node)
                 :nat (do (when-not (and (= 2 (count node)) (integer? (second node)) (not (neg? (second node))))
                            (refuse! "bad :nat node" {:node i}))
                          node)
                 :const (do (when-not (and (= 3 (count node)) (vector? (nth node 2)))
                              (refuse! "bad :const node" {:node i}))
                            [:const (nth constants (position! (second node) n-constants "a constant")) (nth node 2)])
                 :app (do (when-not (= 3 (count node)) (refuse! "bad :app node" {:node i}))
                          [:app (child (nth node 1)) (child (nth node 2))])
                 (:lam :pi) (do (when-not (= 4 (count node)) (refuse! "bad binder node" {:node i}))
                                [(first node) (child (nth node 1)) (child (nth node 2)) (nth node 3)])
                 :let (do (when-not (= 4 (count node)) (refuse! "bad :let node" {:node i}))
                          [:let (child (nth node 1)) (child (nth node 2)) (child (nth node 3))])
                 (refuse! "unknown node tag" {:node i :tag (first node)})))))
     [] nodes)))

(defn- decode-declaration [constants terms declaration]
  (when-not (map? declaration) (refuse! "a declaration must be a map" {}))
  (let [term #(nth terms (position! % (count terms) "a term"))
        constant #(nth constants (position! % (count constants) "a constant"))]
    (cond-> declaration
      (contains? declaration :rainbow/type) (update :rainbow/type term)
      (some? (:rainbow/value declaration)) (update :rainbow/value term)
      (contains? declaration :rainbow/dependencies)
      (update :rainbow/dependencies #(if (coll? %) (into #{} (map constant) %)
                                         (refuse! ":rainbow/dependencies must be a collection" {}))))))

(defn shared? [bundle]
  (= schema-version (:rainbow.bundle/schema-version bundle)))

(defn decode
  "The plain bundle a shared bundle encodes. Refuses anything malformed."
  [bundle]
  (let [payload (:rainbow.bundle/payload-schema bundle)
        constants (:constants bundle)]
    (when-not (#{1 2} payload) (refuse! ":rainbow.bundle/payload-schema must be 1 or 2" {:payload payload}))
    (when-not (and (vector? constants) (every? string? constants) (apply distinct? nil constants))
      (refuse! ":constants must be a vector of distinct id strings" {}))
    (let [terms (decode-terms constants (:terms bundle))
          declaration (partial decode-declaration constants terms)
          plain (-> bundle
                    (dissoc :constants :terms :rainbow.bundle/payload-schema)
                    (assoc :rainbow.bundle/schema-version payload))]
      (case payload
        1 (do (when-not (vector? (:declarations plain)) (refuse! "schema 1 requires :declarations" {}))
              (update plain :declarations #(mapv declaration %)))
        2 (do (when-not (vector? (:entries plain)) (refuse! "schema 2 requires :entries" {}))
              (update plain :entries
                      #(mapv (fn [entry]
                               (if (= :declaration (:entry/kind entry))
                                 (update entry :entry/value declaration)
                                 entry))
                             %)))))))
