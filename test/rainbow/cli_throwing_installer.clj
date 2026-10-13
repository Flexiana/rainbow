(ns rainbow.cli-throwing-installer
  "Test-only installer whose extend-environment throws the way the Bellman fold did on
  2026-09-27 (a kernel alias conflict inside a milestone installer), for cli-test.")

(defn extend-environment [_env]
  (throw (ex-info "Milestone declaration rejected"
                  {:name 'cli-test/duplicated
                   :result {:status :rejected
                            :error {:alias 'cli-test/duplicated
                                    :error/category :kernel/alias-conflict}}})))
