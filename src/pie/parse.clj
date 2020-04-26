(ns pie.parse
  (:require [instaparse.core :as p]
            [clojure.java.io :as io]
            [clojure.walk :as walk]))

(defn make-nat [x]
  (case x
    0 :zero
    [:add1 (make-nat (dec x))]))

(def implicit-tags
  #{:args :piArgs :piArg})

(def replace-tags
  {:eq :=})

(defn postparse [x]
  (walk/postwalk
    (fn [f]
      (cond
        (and (sequential? f)
             (replace-tags (first f)))
        (vec
          (cons
            (-> f first replace-tags)
            (rest f)))
        (and (sequential? f)
             (implicit-tags (first f)))
        (vec (rest f))
        (and (sequential? f)
             (#{:natLit} (first f)))
        (make-nat (Integer/parseInt (second f)))
        (and (sequential? f)
             (= 1 (count f)))
        (first f)
        true
        f))
    x))

(defn parse-raw [txt]
  ((p/parser
     (slurp
       (io/resource "grammar.bnf"))
     :auto-whitespace :standard)
   txt))

(defn parse [txt]
  (postparse
    (parse-raw txt)))

