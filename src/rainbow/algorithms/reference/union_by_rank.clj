(ns rainbow.algorithms.reference.union-by-rank
  "Executable union-find with union by rank + path compression, matching the
  proved attach decision.")

(defn attach-under? [rank-a rank-b] (<= rank-a rank-b))

(defn make-uf [n] {:parent (vec (range n)) :rank (vec (repeat n 0))})

(defn find-root [uf x]
  (let [p (get-in uf [:parent x])]
    (if (= p x) [uf x]
        (let [[uf root] (find-root uf p)]
          [(assoc-in uf [:parent x] root) root]))))

(defn union [uf a b]
  (let [[uf ra] (find-root uf a) [uf rb] (find-root uf b)]
    (if (= ra rb)
      uf
      (let [rka (get-in uf [:rank ra]) rkb (get-in uf [:rank rb])]
        (if (attach-under? rka rkb)
          (cond-> (assoc-in uf [:parent ra] rb)
            (= rka rkb) (update-in [:rank rb] inc))
          (assoc-in uf [:parent rb] ra))))))

(defn connected? [uf a b]
  (= (second (find-root uf a)) (second (find-root uf b))))
