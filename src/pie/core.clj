(ns pie.core
  (:require [clojure.core.match :refer [match]]
            [pie.parse :refer [parse]]
            [pie.unifier :as u]))

(defn run [p]
  (->
    (reduce
      (fn [acc f]
        (match
          f
          [:claim n ex]
          (update acc
                  :types
                  conj
                  [n
                   (u/type-of (:types acc) ex)])
          [:define n ex]
          (update acc
                  :vals
                  conj
                  [n
                   (or (u/check
                         (:types acc)
                         n ex)
                       (throw (ex-info
                                "Typecheck failure"
                                {:name       n
                                 :expression ex
                                 :ostensible-type
                                             (second (first (->> acc :types
                                                                 (filter (comp #{n} first)))))})))])))
      {}
      p)
    (update :types (partial into {}))
    (update :vals (partial into {}))))

(defn eval-pi [txt]
  (run (parse txt)))

