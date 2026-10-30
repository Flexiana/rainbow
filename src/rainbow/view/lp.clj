(ns rainbow.view.lp
  "`lein lp-view <instance.edn> <certificate.edn> [out-dir]`: run the LP optimality certificate
  checker (rainbow.or.lp-certificate/certify) and write the LP Certificate Viewer: index.html with
  its data inline, and lp-view.json.

  The instance is what certify reads, {:matrix :capacities :margins} with optional :sense
  (:maximize, :minimize) and :equalities [{:row :value}]; the certificate is {:plan :prices} with
  :equality-prices when there are equalities. Numbers are exact rationals. Optional text for the
  page (:title :story :source :objective-label, :variables [{:name :label}], :constraints
  [\"..\"]) may sit in the instance file; it is shown as given and never checked.

  Untrusted. The verdict is certify's: the kernel checks one instance of
  optimization/signed-lp-optimality-certificate-on. The page also shows each comparison that proof
  is built from, every number of them confirmed by its own kernel check, so a refused certificate
  names the comparison that failed. Negative controls (the same checks with a number off by one)
  must be refused, or nothing is written."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.view :as view]))

(def default-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(defn environment
  "The checkpoint (replayed by the kernel) with the LP duality and signed-order modules."
  ([] (environment default-checkpoint))
  ([path] (let [r (checkpoint/load-checkpoint path)]
            (when-not (= :replayed (:status r)) (throw (ex-info (str "checkpoint did not replay: " path) {:result (dissoc r :environment)})))
            (-> (:environment r) lp-on/extend-environment decide-order/extend-environment))))

(defn- q [v] (str (rationalize v)))
(defn- dot [a b] (reduce + 0 (map * (map rationalize a) (map rationalize b))))
(def ^:private szero (f/const* 'signed/zero []))
(defn- call [name & args] (apply f/app (f/const* name []) args))

(defn- kcheck
  "Elaborate and kernel-check value : type; {:kernel :checked} or {:kernel :rejected :category ..}."
  [env value type]
  (let [v (elaborate/core-expression env value) t (elaborate/core-expression env type)]
    (if (and (= :elaborated (:status v)) (= :elaborated (:status t)))
      (let [r (kernel/check env (:term v) (:term t))]
        (cond-> {:kernel (:status r)} (not= :checked (:status r)) (assoc :category (get-in r [:error :error/category]))))
      {:kernel :rejected :category :elaboration-failed})))

(defn- confirm
  "The kernel confirms that term equals the exact rational value."
  [env term value]
  (let [l (#'lp/signed-literal value)]
    (assoc (kcheck env (#'lp/computed-equivalence term l) (#'lp/seq-equiv term l)) :value (q value))))

(defn- decide [env a b] (kcheck env (#'lp/decided-at-most a b) (#'lp/sle a b)))

(defn steps
  "Every comparison of the certificate, each decided by the kernel on its own, for an instance in
  standard form (maximize, <= rows), plus the negative controls."
  [env {:keys [matrix capacities margins plan prices] :as instance}]
  (let [{:keys [x y b c row-activity dual-price objective dual-objective]} (#'lp/instance-terms instance)
        sadd #(call 'signed/add %1 %2) sneg #(call 'signed/negate %)
        primal (dot margins plan) dual (dot capacities prices)]
    {:rows (vec (for [i (range (count capacities)) :let [act (dot (matrix i) plan) at (f/app (row-activity x) [:nat i])
                                                         bt (f/app b [:nat i]) slack (- (rationalize (capacities i)) act)]]
                  {:index i :activity (confirm env at act) :capacity (q (capacities i))
                   :within-capacity (decide env at bt) :slack (confirm env (sadd bt (sneg at)) slack)
                   :price (q (prices i)) :price-nonnegative (decide env szero (f/app y [:nat i]))
                   :binding (zero? slack) :complementary (q (* slack (rationalize (prices i))))}))
     :columns (vec (for [j (range (count margins)) :let [price (dot (map #(nth % j) matrix) prices) pt (f/app dual-price [:nat j])
                                                         ct (f/app c [:nat j]) reduced (- price (rationalize (margins j)))]]
                     {:index j :plan (q (plan j)) :margin (q (margins j))
                      :plan-nonnegative (decide env szero (f/app x [:nat j]))
                      :column-price (confirm env pt price) :covers-margin (decide env ct pt)
                      :reduced-cost (confirm env (sadd pt (sneg ct)) reduced) :complementary (q (* reduced (rationalize (plan j))))}))
     :primal-objective (confirm env (objective x) primal)
     :dual-objective (confirm env dual-objective dual)
     :objectives-equal (kcheck env (#'lp/computed-equivalence dual-objective (objective x)) (#'lp/seq-equiv dual-objective (objective x)))
     :gap (q (- dual primal))
     :controls {:objective-off-by-one (confirm env (objective x) (inc primal))
                :activity-off-by-one (confirm env (f/app (row-activity x) [:nat 0]) (inc (dot (matrix 0) plan)))
                :capacity-exceeded (decide env (#'lp/signed-literal (inc (rationalize (capacities 0)))) (f/app b [:nat 0]))}}))

(defn- as-vectors
  "The data with every vector a Clojure vector, so that the steps can index it (EDN may hold a
  list). A vector is returned as itself, so the data certify sees, and its audit id, are unchanged."
  [data]
  (cond-> (reduce (fn [d k] (if (sequential? (get d k)) (update d k vec) d))
                  data [:capacities :margins :plan :prices :equality-prices])
    (sequential? (:matrix data)) (update :matrix #(mapv vec %))
    (sequential? (:equalities data)) (update :equalities #(mapv (fn [e] (update e :row vec)) %))))

(defn checked-data
  "What certify is given: the instance's LP fields with the certificate's. Throws, naming the field,
  when the shape is wrong (rainbow.or.lp-certificate/shape-problem): a plan or price vector of the
  wrong length or an entry that is not an exact rational is refused before anything is checked or
  written, never shown as certified."
  [instance certificate]
  (let [checked (merge (select-keys instance [:matrix :capacities :margins :sense :equalities])
                       (select-keys certificate [:plan :prices :equality-prices]))]
    (when-let [problem (lp/shape-problem checked)]
      (throw (ex-info (:message problem) (assoc (dissoc problem :status) :lp-view/refused :shape))))
    (as-vectors checked)))

(defn example
  "The viewer's data for one instance and certificate: certify's verdict and the step-by-step check."
  [env instance certificate]
  (let [checked (checked-data instance certificate)
        standard (#'lp/standard-form checked)
        t0 (System/nanoTime)
        result (lp/certify env checked {:alias 'optimization/lp-view-certificate})
        ms (Math/round (/ (- (System/nanoTime) t0) 1e6))
        n (count (:margins standard)) m (count (:capacities standard))]
    {:id "certificate" :kind :optimality
     :title (:title instance "LP certificate") :story (:story instance "") :source (:source instance "Supplied by the user; not checked.")
     :objective-label (:objective-label instance "objective")
     :variables (or (:variables instance) (vec (for [j (range n)] {:name (str "x" (inc j)) :label ""})))
     :constraints (vec (concat (:constraints instance) (for [i (range (count (:constraints instance)) m)] (str "Row " (inc i)))))
     :instance {:matrix (mapv #(mapv q %) (:matrix standard)) :capacities (mapv q (:capacities standard)) :margins (mapv q (:margins standard))
                :plan (mapv q (:plan standard)) :prices (mapv q (:prices standard)) :sense :maximize
                :note (when (not= standard checked)
                        (str (when (= :minimize (:sense checked)) "The cost problem is shown as the maximization of the negated costs. ")
                             (when (seq (:equalities checked)) "Each equality row is shown as two <= rows, its free price split into two nonnegative prices. ")
                             "This is the form the checker proves things about."))}
     :certify {:function "rainbow.or.lp-certificate/certify" :status (:status result) :objective (some-> (:objective result) q)
               :sense (:sense result) :kernel-category (some-> (:kernel/category result) str) :message (when (= :rejected (:status result)) (:message result))
               :declarations (vec (for [[nm {:keys [id status axioms]}] (:declarations result)]
                                    {:name (str nm) :id (str id) :status status :axioms (mapv str axioms)}))
               :audit-id (:audit/id result) :milliseconds ms}
     :steps (steps env standard)}))

(defn view-data
  "The data the LP Certificate Viewer reads."
  [env instance certificate]
  (let [e (example env instance certificate)]
    (doseq [[label c] (:controls (:steps e))]
      (when-not (= :rejected (:kernel c)) (throw (ex-info (str "negative control accepted: " (name label) "; nothing written") {:control label}))))
    {:generated-by "lein lp-view" :generated (str (java.time.Instant/now))
     :theorems {:optimality {:name "optimization/signed-lp-optimality-certificate-on"
                             :axioms (mapv str (kernel/axioms env 'optimization/signed-lp-optimality-certificate-on))}}
     :examples [e]}))

(def ^:private usage
  "usage: lein lp-view <instance.edn> <certificate.edn> [out-dir] [--checkpoint path] [--offline]")

(defn- failure
  "An ex-info carrying the FAIL line lp-view prints: what failed, why, and what to check."
  [what why check]
  (ex-info why {:lp-view/fail {:what what :why why :check check}}))

(defn- read-map
  "The EDN map in the file at path, or a failure naming the file."
  [role path]
  (let [what (str role " " path) file (io/file path)]
    (when-not (.exists file)
      (throw (failure what "no such file" (str "Check the path of the " role " file."))))
    (when-not (.isFile file)
      (throw (failure what "not a file" (str "Name the " role " EDN file, not a directory."))))
    (let [value (try (edn/read-string (slurp file))
                     (catch Exception e
                       (throw (failure what (str "not readable EDN: " (or (.getMessage e) (.getName (class e))))
                                       "Check that the file is complete EDN, with every bracket closed."))))]
      (when-not (map? value)
        (throw (failure what (str "not an EDN map but " (if (nil? value) "an empty file" (pr-str (type value))))
                        (if (= "instance" role)
                          "The instance is a map {:matrix [[..]] :capacities [..] :margins [..]}."
                          "The certificate is a map {:plan [..] :prices [..]}."))))
      value)))

(defn- load-environment [path]
  (try (environment path)
       (catch Exception e
         (throw (failure (str "--checkpoint " path) (or (.getMessage e) (.getName (class e)))
                         (str "Check that --checkpoint names a kernel checkpoint (.edn.gz) that exists; "
                              "without the flag lp-view uses " default-checkpoint ", run from the Rainbow directory."))))))

(defn run
  "lein lp-view: reads the files, checks the certificate, writes the page; returns the exit code (0
  certified, 1 refused or failed, 2 usage). A file that is missing or not EDN, data of the wrong
  shape and a checkpoint that does not replay each print one FAIL line saying what to check, and
  nothing is written."
  [args]
  (let [[[instance-path certificate-path out] opts] (view/parse-args args #{"--offline"})]
    (if-not certificate-path
      (do (println usage) 2)
      (try
        (when (and (contains? opts :checkpoint) (not (string? (:checkpoint opts))))
          (throw (failure "--checkpoint" "no path given" "Write --checkpoint <path to checkpoint.edn.gz>, or leave the flag out.")))
        (let [out (or out "lp-view")
              instance (read-map "instance" instance-path)
              certificate (read-map "certificate" certificate-path)
              _ (try (checked-data instance certificate)
                     (catch clojure.lang.ExceptionInfo e
                       (throw (failure (str instance-path " " certificate-path)
                                       (str (.getMessage e) " (" (:error/category (ex-data e)) ")")
                                       (str "Check that :plan has one entry per column (:margins), :prices one per row "
                                            "(:capacities), each :matrix row one per column, and that every number is "
                                            "an exact rational such as 3 or 3/2.")))))
              env (load-environment (:checkpoint opts default-checkpoint))
              data (try (view-data env instance certificate)
                        (catch Exception e
                          (throw (failure (str instance-path " " certificate-path) (or (.getMessage e) (.getName (class e)))
                                          "Nothing was written; check the instance and certificate files."))))
              {:keys [status objective kernel-category]} (:certify (first (:examples data)))]
          (try (view/write-page! out "scripts/lp-view.html" "lp-view.json" data (:offline opts))
               (catch Exception e
                 (throw (failure (str "-> " out) (or (.getMessage e) (.getName (class e)))
                                 "Check that the output directory is writable, and run lp-view from the Rainbow directory (it reads scripts/lp-view.html)."))))
          (println "wrote" (str out "/index.html") "and lp-view.json; certify:" (name status) (or objective kernel-category ""))
          (if (= :certified status) 0 1))
        (catch clojure.lang.ExceptionInfo e
          (if-let [{:keys [what why check]} (:lp-view/fail (ex-data e))]
            (println "FAIL lp-view" what "--" why "--" check)
            (println "FAIL lp-view --" (.getMessage e) "-- Check the instance, certificate and --checkpoint arguments."))
          1)
        (catch Exception e
          (println "FAIL lp-view --" (or (.getMessage e) (.getName (class e)))
                   "-- Check the instance, certificate and --checkpoint arguments.")
          1)))))

(defn -main [& args]
  (let [code (run args)]
    (shutdown-agents)
    (System/exit code)))
