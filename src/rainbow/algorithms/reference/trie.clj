(ns rainbow.algorithms.reference.trie
  "Executable trie (prefix tree), matching the proved word/prefix membership.")

(defn is-word? [path-complete? terminal?] (and path-complete? terminal?))

(def empty-trie {})

(defn insert [trie word]
  (update-in trie (concat word [:terminal]) (constantly true)))

(defn- walk [trie word]
  (get-in trie word ::missing))

(defn contains-word?
  "True iff word is a stored word (complete path AND terminal)."
  [trie word]
  (let [node (walk trie word)]
    (is-word? (not= node ::missing)
              (boolean (and (map? node) (:terminal node))))))

(defn has-prefix?
  "True iff some stored word starts with prefix."
  [trie prefix]
  (not= (walk trie prefix) ::missing))
