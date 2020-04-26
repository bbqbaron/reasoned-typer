(ns pie.core-test
  (:require [clojure.test :refer [deftest testing is]]
            [pie.core :as c :refer [eval-pi]]
            [pie.parse :as parse])
  (:import clojure.lang.ExceptionInfo))

(defmacro fails-with [data & ops]
  `(try
     ~@ops
     (is false "expected failure")
     (catch ExceptionInfo e#
       (is
         (= ~data (ex-data e#))))))

(deftest a-test
  (is
    (=
      {:types {"a" [:Vec :Nat :zero]}
       :vals  {"a" :vecnil}}
      (eval-pi
        "(claim a (Vec Nat 0))
   (define a vecnil)"))))

(deftest check-fail
  (fails-with
    {:name            "a"
     :expression      :zero
     :ostensible-type [:Vec :Nat :zero]}
    (eval-pi
      "(claim a (Vec Nat 0))
  (define a zero)")))

(deftest application
  (is
    (=
      {:types {"a" :Nat} :vals {"a" [:apply [:lam ["x"] :zero] :zero]}}
      (eval-pi
        "
   (claim a Nat)
   (define a
    ((the
     (Pi ((x Nat)) Nat)
     (lam (x) zero))
     zero))"))))

(deftest which-nat
  (is
    (= {:types {"a" :Nat}
        :vals  {"a" [:whichNat :zero [:the :Nat :zero] [:lam ["x"] :zero]]}}
       (c/eval-pi
         "(claim a Nat)
  (define a
  (which-Nat
   zero
   zero
   (the
    (Pi ((x Nat)) Nat)
    (lam (x) zero))))"))))

(deftest which-nat-nonzero
  (is
    (= {:types {"a" :Nat}
        :vals
               {"a"
                [:whichNat
                 [:add1 [:add1 [:add1 [:add1 :zero]]]]
                 [:the :Nat [:add1 :zero]]
                 [:lam ["x"] [:add1 [:ref "x"]]]]}}
       (c/eval-pi
         "(claim a Nat)
  (define a
  (which-Nat
   4
   1
   (the
    (Pi ((x Nat)) Nat)
    (lam (x) (add1 x)))))")))

  (is
    (= {:types
              {"a"
               [:=
                :Nat
                :zero
                [:whichNat :zero [:the :Nat :zero] [:lam ["x"] [:ref "x"]]]]},
        :vals {"a" [:same [:apply [:lam ["x"] :zero] :zero]]}}
       (c/eval-pi
         "(claim a (= Nat 0 (which-Nat
   0
   0
   (the
    (Pi ((x Nat)) Nat)
    (lam (x) x)))))
  (define a
  (same ((the (Pi ((x Nat)) Nat) (lam (x) zero)) zero)))"))))

(deftest eq
  (is
    (= {:types {"a" [:= :Nat [:add1 [:add1 :zero]] [:add1 [:add1 :zero]]]}
        :vals  {"a" [:same [:add1 [:add1 :zero]]]}}
       (c/eval-pi
         "(claim a (= Nat 2 2))
  (define a (same 2))")))
  (fails-with
    {:name       "a"
     :expression [:same [:add1 [:add1 :zero]]]
     :ostensible-type
                 [:= :Nat [:add1 [:add1 :zero]] [:add1 [:add1 [:add1 :zero]]]]}
    (c/eval-pi
      "(claim a (= Nat 2 3))
  (define a (same 2))")))

