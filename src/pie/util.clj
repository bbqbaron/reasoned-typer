(ns pie.util)

(defn ind-vec-step [motive E]
  [:Pi [['k :Nat]]
   [:Pi [['el E]]
    [:Pi [['els [:Vec E 'k]]]
     [:Pi [['almost [[motive 'k] 'els]]]
      [[motive [:add1 'k]]
       [:veccons 'el 'els]]]]]])

(defn ind-vec-motive [E]
  [:Pi [['k :Nat]]
   [:Pi [['els [:Vec E 'k]]]
    :U]])
