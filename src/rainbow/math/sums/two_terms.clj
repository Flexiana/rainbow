(ns rainbow.math.sums.two-terms
  "One term, and two DISTINCT terms, are bounded by a nonnegative expr-sum-value.
  Reuses the existing sum and order. F is intentionally not named q: s/induct binds q."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.environment :as environment]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat family call at sum le below]]
            [rainbow.math.sums.nonneg-zero :as nonnegative]))

(def tl [:succ [:zero]])
(defn add [x y] (call 'signed/add x y))
(defn eqn [x y] (f/equality tl nat x y))
(defn neqn [x y] (call 'proposition/negation (eqn x y)))
(defn nsym [x y h] (f/app (f/const* 'equality/symmetric [tl]) nat x y h))
(defn ntrans [x y z h k] (f/app (f/const* 'equality/transitive [tl]) nat x y z h k))
(defn subst [x y h P px] (f/app (f/const* 'equality/substitution [tl]) nat x y h P px))
(defn letrans [x y z h k] (call 'signed/at-most-transitive x y z h k))
(defn impossible-bound [i hi goal]
  (call 'proposition/explode goal
        (at (call 'nat/zero-not-successor i)
            (nsym (s/succ i) s/nz (call 'nat/equal-zero-of-at-most-zero (s/succ i) hi)))))
(defn split-last [i hi limit goal at-last before-last]
  (call 'proposition/use-disjunction (eqn i limit) (below i limit) goal
        (call 'nat/at-most-split i limit (call 'nat/at-most-successor-cancel-local i limit hi))
        at-last before-last))
(defn prefix-nonnegative [limit]
  (f/lam [['pi nat] ['pb (below 'pi limit)]] (at 'hF 'pi (s/weaken 'pi limit 'pb))))
(defn prefix-at-most-total [limit]
  (let [head (sum 'F limit) tail (at 'F limit) total (add head tail)]
    (s/le-transport (add head s/zero) head total total
                    (call 'signed/add-zero-right head) (s/refl total)
                    (call 'signed/add-left-monotone s/zero tail head (at 'hF limit (s/self-below limit))))))

(def term-bound-spec
  (let [claim (fn [length]
                (f/forall [['hF (s/all-below length #(le s/zero (at 'F %)))]
                           ['i nat] ['hi (below 'i length)]]
                          (le (at 'F 'i) (sum 'F length))))]
    (s/spec 'signed/expr-sum-value-term-bound [['F family] ['n nat]] (claim 'n)
      (s/induct claim
        (f/lam [['hF (s/all-below s/nz #(le s/zero (at 'F %)))] ['i nat] ['hi (below 'i s/nz)]]
               (impossible-bound 'i 'hi (le (at 'F 'i) (sum 'F s/nz))))
        (fn [limit ih]
          (let [head (sum 'F limit) tail (at 'F limit) total (sum 'F (s/succ limit))
                hprefix (prefix-nonnegative limit)
                head0 (call 'signed/expr-sum-value-nonnegative 'F limit hprefix)
                tail-le (s/le-transport (add s/zero tail) tail total total
                                        (s/trans (add s/zero tail) (add tail s/zero) tail (call 'signed/add-commutative s/zero tail) (call 'signed/add-zero-right tail)) (s/refl total)
                                        (call 'signed/add-right-monotone s/zero head tail head0))]
            (f/lam [['hF (s/all-below (s/succ limit) #(le s/zero (at 'F %)))]
                    ['i nat] ['hi (below 'i (s/succ limit))]]
              (split-last 'i 'hi limit (le (at 'F 'i) total)
                (f/lam [['ie (eqn 'i limit)]]
                  (subst limit 'i (nsym 'i limit 'ie)
                         (f/lam [['ti nat]] (le (at 'F 'ti) total)) tail-le))
                (f/lam [['ib (below 'i limit)]]
                  (letrans (at 'F 'i) head total (at ih hprefix 'i 'ib) (prefix-at-most-total limit)))))))
        'n))))

(def two-distinct-bound-spec
  (let [goal (fn [length i j] (le (add (at 'F i) (at 'F j)) (sum 'F length)))
        binders (fn [length]
                  [['hF (s/all-below length #(le s/zero (at 'F %)))]
                   ['i nat] ['hi (below 'i length)] ['j nat] ['hj (below 'j length)]
                   ['hne (neqn 'i 'j)]])
        claim (fn [length] (f/forall (binders length) (goal length 'i 'j)))]
    (s/spec 'signed/expr-sum-value-two-distinct-bound [['F family] ['n nat]] (claim 'n)
      (s/induct claim
        (f/lam (binders s/nz) (impossible-bound 'i 'hi (goal s/nz 'i 'j)))
        (fn [limit ih]
          (let [head (sum 'F limit) tail (at 'F limit) length (s/succ limit)
                total (sum 'F length) hprefix (prefix-nonnegative limit)
                before (fn [i hi] (call 'signed/expr-sum-value-term-bound 'F limit hprefix i hi))
                last-before (s/le-transport (add tail (at 'F 'j)) (add tail (at 'F 'j))
                                           (add tail head) total (s/refl (add tail (at 'F 'j)))
                                           (call 'signed/add-commutative tail head)
                                           (call 'signed/add-left-monotone (at 'F 'j) head tail (before 'j 'jb)))
                before-last (call 'signed/add-right-monotone (at 'F 'i) head tail (before 'i 'ib))]
            (f/lam (binders length)
              (split-last 'i 'hi limit (goal length 'i 'j)
                (f/lam [['ie (eqn 'i limit)]]
                  (split-last 'j 'hj limit (goal length 'i 'j)
                    (f/lam [['je (eqn 'j limit)]]
                      (call 'proposition/explode (goal length 'i 'j)
                            (at 'hne (ntrans 'i limit 'j 'ie (nsym 'j limit 'je)))))
                    (f/lam [['jb (below 'j limit)]]
                      (subst limit 'i (nsym 'i limit 'ie)
                             (f/lam [['ti nat]] (goal length 'ti 'j)) last-before))))
                (f/lam [['ib (below 'i limit)]]
                  (split-last 'j 'hj limit (goal length 'i 'j)
                    (f/lam [['je (eqn 'j limit)]]
                      (subst limit 'j (nsym 'j limit 'je)
                             (f/lam [['tj nat]] (goal length 'i 'tj)) before-last))
                    (f/lam [['jb (below 'j limit)]]
                      (letrans (add (at 'F 'i) (at 'F 'j)) head total
                               (at ih hprefix 'i 'ib 'j 'jb 'hne) (prefix-at-most-total limit)))))))))
        'n))))

(def theorem-specs [term-bound-spec two-distinct-bound-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.nonneg-zero])

(defn install
  "Adds this module's own declarations."
  [env]
  (let [env (if (environment/resolve-id env 'signed/expr-sum-value-nonnegative-terms-zero) env env)] (reduce (fn [e spec] (println :two-terms :installing (:name spec)) (flush) (support/add-spec-shared e :expr-sum-two-terms spec)) env theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.two-terms))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
