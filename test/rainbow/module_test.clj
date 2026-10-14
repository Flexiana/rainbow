(ns rainbow.module-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.environment :as environment]
            [rainbow.module :as module]))

(deftest dependency-order-is-stable-and-deduplicates-diamonds
  (with-redefs [module/deps {'root ['left 'right] 'left ['shared]
                            'right ['shared] 'shared []}]
    (is (= ['shared 'left 'right 'root] (module/order ['root])))
    (is (= ['shared 'right 'left 'root] (module/order ['right 'root 'root])))
    (is (= [] (module/order [])))))

(deftest dependency-cycles-are-rejected
  (doseq [graph [{'a ['a]} {'a ['b] 'b ['c] 'c ['a]}]]
    (with-redefs [module/deps graph]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"module dependency cycle"
                            (module/order ['a]))))))

(defn- with-modules [modules f]
  ;; Replace namespace resolution only. The real dependency traversal, environment
  ;; bookkeeping, legacy fallback and installer calls are all exercised.
  (with-redefs-fn {#'module/module-var
                  (fn [n v]
                    (when-let [value (get-in modules [n v])]
                      (if (= v 'deps) (atom value) value)))}
    f))

(deftest each-module-installs-once-per-environment
  (let [calls (atom [])
        install (fn [n] (fn [env] (swap! calls conj n) env))
        modules {'root {'deps ['left 'right] 'install (install 'root)}
                 'left {'deps ['shared] 'install (install 'left)}
                 'right {'deps ['shared] 'install (install 'right)}
                 'shared {'deps [] 'install (install 'shared)}}
        base (environment/empty-environment)]
    (with-modules modules
      (fn []
        (let [env (module/install-module base 'root)]
          (is (= ['shared 'left 'right 'root] @calls))
          (is (= #{'shared 'left 'right 'root} (module/installed env)))
          (is (= env (module/install-module env 'root)))
          (is (= 4 (count @calls)))
          (is (= (environment/environment-id base) (environment/environment-id env)))
          (module/install-module base 'root)
          (is (= 8 (count @calls)) "a fresh environment must not reuse another's install markers"))))))

(deftest legacy-installers-and-custom-dependencies-share-bookkeeping
  (let [calls (atom [])
        modules {'root {'deps ['legacy 'shared]
                        'install (fn [env] (swap! calls conj 'root) env)}
                 'legacy {'extend-environment (fn [env]
                                                (swap! calls conj 'legacy)
                                                (module/install-module env 'shared))}
                 'shared {'install (fn [env] (swap! calls conj 'shared) env)}}]
    (with-modules modules
      (fn []
        (let [env (module/install-module (environment/empty-environment) 'root)]
          (is (= ['legacy 'shared 'root] @calls))
          (is (= #{'root 'legacy 'shared} (module/installed env))))))))

(deftest missing-and-failed-installers-cannot-succeed
  (with-modules {'missing {'deps []}}
    #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"neither install nor extend-environment"
                          (module/install-module {} 'missing))))
  (let [calls (atom 0)
        base (environment/empty-environment)]
    (with-modules {'broken {'install (fn [_]
                                      (swap! calls inc)
                                      (throw (ex-info "declaration rejected" {})))}}
      (fn []
        (dotimes [_ 2]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"declaration rejected"
                                (module/install-module base 'broken))))
        (is (= 2 @calls))
        (is (empty? (module/installed base)))))))

(deftest malformed-installer-results-cannot-be-marked-installed
  (doseq [result [nil {} [] false
                  (assoc (environment/empty-environment) :rainbow.environment/aliases nil)]]
    (let [dependent-calls (atom 0)
          modules {'broken {'install (constantly result)}
                   'root {'deps ['broken]
                          'install (fn [env] (swap! dependent-calls inc) env)}}]
      (with-modules modules
        (fn []
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not return a declaration environment"
                                (module/install-module (environment/empty-environment) 'root)))
          (is (zero? @dependent-calls)))))))
