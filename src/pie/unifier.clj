(ns pie.unifier
  (:require [clojure.core.logic :as l :refer [conda
                                              conde
                                              condu
                                              defna defne fresh run s# u#]]
            [pie.util :as u]))

(declare isao)
(declare typeo)
(declare sameo)
(declare sametypeo)
(declare syntho)

(defn symbolo [s]
  (l/== s (gensym)))

(defna lookupo [ac ax aT]
       ([[] _ _]
        u#)
       ([[[x T]] x T])
       ([[[x Q]] x T]
        u#)
       ([[[x T] . _] x T])
       ([[[x Q] . _] x T]
        u#)
       ([[[y _] . more] x T]
        (lookupo more x T)))

(defna unboundo [ac ax]
       ([[] _])
       ([[[x _]] x]
        u#)
       ([[[x _] . _] x]
        u#)
       ([[[y _] . more] x]
        (unboundo more x)))

(defna typeo [ac av aT aT2]
       ([c v :Atom :Atom])
       ([c v :Nat :Nat])
       ([c v :Trivial :Trivial])
       ([c v :Absurd :Absurd])
       ([c v :U :U])

       ([c v [:Pair a d] [:Sig [[x Ao]] Do]]
        (fresh [h c2]
               (typeo c v a Ao)
               (l/conso [x Ao] c c2)
               (typeo c2 v d Do)))

       ([c v [:Sig [[x A] . More] D]
         [:Sig [[xo Ao]]
          Do]]
        (fresh [c2]
               (typeo c v A Ao)
               (l/conso [x Ao] c c2)
               (typeo c2 v
                      [:Sig More D]
                      Do)))
       ([c v [:Sig [[x A]] D]
         [:Sig [[xo Ao]]
          Do]]
        (fresh [c2]
               (typeo c v A Ao)
               (l/conso [x Ao] c c2)
               (typeo c2 v D Do)))

       ([c v [:Pi [[x A]] R] [:Pi [[x Ao]] Ro]]
        (fresh [c2]
               (typeo c v A Ao)
               (l/conso [x Ao] c c2)
               (typeo c2 v R Ro)))
       ; TODO multi-arity Pi sugar
       ([c v [:List e] [:List eo]]
        (typeo c v e eo))

       ([c v [:Vec E l] [:Vec Eo lo]]
        (isao c v l :Nat lo)
        (typeo c v E Eo))

       ([c v [:= X from to] [:= Xo fromo too]]
        (typeo c v X Xo)
        (isao c v from Xo fromo)
        (isao c v to Xo too))

       ([c v [:Either P S] [:Either Po So]]
        (typeo c v P Po)
        (typeo c v S So))

       ([c v e ct]
        (isao c v e :U ct)))

(defna sametypeo [ac av aX aX2]
       ([c v :Atom :Atom])

       ([c v [:Sig [[x A]] D]
         [:Sig [[x2 A2]] D2]]
        (sametypeo c v A A2)
        (fresh [c2]
               (l/conso [x A] c c2)
               (sametypeo
                 c2 D D2)))

       ([c v [:Pi [[x A]] R] [:Pi [[x2 A2]] R2]]
        (sametypeo c v A A2)
        (fresh [c2]
               (l/conso [x A] c c2)
               (sametypeo
                 c2 v R R2)))

       ([c v :Nat :Nat])

       ([c v [:List E] [:List Eo]]
        (sametypeo c v E Eo))

       ([c v [:Vec E l] [:Vec E2 l2]]
        (sametypeo c v E E2)
        (sameo c v l l2 :Nat))

       ([c v [:= X from to]
         [:= X2 from2 to2]]
        (sametypeo c v X X2)
        (sameo c v from from2 X)
        (sameo c v to to2 X2))

       ([c v [:Either P S] [:Either Po So]]
        (sametypeo c v P Po)
        (sametypeo c v S So))

       ([c v :Trivial :Trivial])

       ([c v :Absurd :Absurd])

       ([c v :U :U])
       ([c v a b]
        (sameo c v a b :U)))

(defna isao [ac av ae aT ae2]
       ([c v :nil [:List T] :nil])

       ([c v :vecnil [:Vec T :zero] :vecnil])

       ([c v [:cons a d] [:Sig [[x A]] D]
         [:cons ao do]]
        (isao c v a A ao)
        (isao c v d [:apply [:lam [x] d] ao] do))

       ([c v [::vec el els]
         [:Vec E [:add1 l]]
         [::vec elo elso]]
        (isao c v el E elo)
        (isao c v els [:Vec E l] elso))

       ([c v [:same mid] [:= X from to]
         [:same mido]]
        (isao c v mid X mido)
        (sameo c v from mido X)
        (sameo c v mido to X))

       ([c v [:left lt] [:Either P _] [:left lto]]
        (isao c v lt P lto))
       ([c v [:right rt] [:Either _ S] [:right rto]]
        (isao c v rt S rto))

       ([c v [:lam [x] r]
         [:Pi [[x A]] R]
         [:lam [x] ro]]
        (fresh [c2]
               (l/conso [x A] c c2)
               (isao c2 v r R ro)))

       ;; TODO multi-arity lambda sugar

       ([c v e X2 eo]
        (fresh [X1]
               (syntho c v e X2 eo)
               (sametypeo c v X1 X2))))

(defna syntho [ac av ae aT ae2]
       ([c v [:ref e] Xo eo]
        (lookupo c e Xo)
        (conde
          ((l/== eo [:ref e]))
          ((lookupo v e eo))))

       ([c v e :Atom e]
        (symbolo e))

       ([c v :zero :Nat :zero])
       ([c v [:add1 n] :Nat [:add1 no]]
        (isao c v n :Nat no))
       ([c v [:ind-Nat t m b s]
         [:apply mo to]
         [:ind-Nat to mo bo so]]
        (isao c v t :Nat to)
        (isao c v m [:Pi [['x :Nat]] :U] mo)
        (isao c v [:apply m :zero] b bo)
        (isao c v s [:Pi [['x :Nat]] [:Pi [['b [:apply mo 'x]]
                                           [:apply mo [:add1 'x]]]]]
              so))
       ;; begin recursives

       ([c v [:car p]
         ca [:car po]]
        (fresh [d x]
               (syntho c v p
                       [:Sig [[x ca]] d]
                       po)))
       ([c v [:cdr p]
         subbed [:cdr po]]
        (fresh [x ca cd]
               (syntho c v p
                       [:Sig [[x ca]] cd]
                       po)
               (sametypeo c v
                          subbed
                          [:apply
                           [:lam [x] cd]
                           [:car po]])))

       ([c v [:whichNat t b s]
         Bo
         [:whichNat
          to
          [:the Bo bo]
          so]]
        (isao c v t :Nat to)
        (syntho c v b Bo bo)
        (fresh [x]
               (isao c v s
                     [:Pi [[x :Nat]] Bo]
                     so)))
       ([c v [:iter-Nat t b s]
         Bo
         [:iter-Nat to [:the Bo bo] so]]
        (syntho c v b Bo bo)
        (isao c v t Bo to)
        (fresh [x]
               (isao c v s [:Pi [[x :Nat]] Bo])))
       ([c v [:rec-Nat t b s]
         B
         [:rec-Nat to [:the Bo bo] so]]
        (syntho c v b Bo bo)
        (isao c v t :Nat to)
        (isao c v s [:Pi [['x :Nat]] [:Pi [['b Bo]] Bo]] so))

       ([c v [:lcons e es]
         [:List E]
         [:lcons eo eso]]
        (fresh [Eo]
               (syntho c v e Eo eo)
               (isao c v es [:List Eo] eso)))
       ([c v [:rec-List t b s]
         Bo
         [:rec-List to [:the Bo bo] so]]
        (syntho c v b Bo bo)
        (fresh [Eo ex esx bx]
               (syntho c v t [:List Eo] to)
               (isao c v s
                     [:Pi [[ex Eo]] [:Pi [[esx [:List Eo]]]
                                     [:Pi [[bx Bo]]]]]
                     so)))
       ([c v [:ind-List t m b s]
         [:apply mo to]
         [:ind-List
          to mo bo so]]
        (fresh [To Eo]
               (syntho c
                       t To to)
               (l/== [:List Eo] To)
               (isao c v m [:Pi [['x Eo]] :U]
                     mo)
               (isao c v b [mo :nil] bo)
               (isao c v s
                     [:Pi [['e Eo]]
                      [:Pi [['es [:List Eo]]
                            [:Pi [['b [:apply mo 'es]]]
                             [:apply mo [:lcons 'e 'es]]]]]]
                     so)))

       ([c v [:head els] E [:head elso]]
        (fresh [l]
               (syntho c
                       els [:Vec E [:add1 l]] elso)))
       ([c v [:tail els] [:Vec E l] [:tail elso]]
        (syntho c
                els [:List E [:add1 l]] elso))
       ([c v [:ind-Vec l t m b s] [[:apply mo lo] to]
         [:ind-Vec lo to mo bo so]]
        (fresh [E n]
               (isao c v l :Nat lo)
               (syntho c v t [:Vec E n] to)
               (sameo c v lo n :Nat)
               (isao c v m (u/ind-vec-motive E) mo)
               (isao c v b [[:apply mo :zero] :vecnil] bo)
               (isao c v s (u/ind-vec-step mo E) so)))

       ([c v [:replace t m b] [:apply mo to] [:replace t-o mo bo]]
        (fresh [X from x]
               (syntho c v t [:= X from to] t-o)
               (isao c v m [:Pi [[x X]] :U] mo)
               (isao c v b [:apply mo from] bo)))
       ([c v [:cong t f] [:= Y [:apply fo from] [:apply fo to]] [:cong X1 t-o fo]]
        (fresh [x X2]
               (symbolo x)
               (syntho c v t [:= X1 from to] t-o)
               (syntho c v f [:Pi [[x X2]] Y] fo)
               (sametypeo c v X1 X2)))
       ([c v [:symm t] [:= X to from] [:symm t-o]]
        (syntho c v t [:= X from to] t-o))
       ([c v [:trans t1 t2] [:= X from to] [:trans to1 to2]]
        (fresh [mid1 mid2 Y]
               (syntho c v t1 [:= X from mid1] to1)
               (syntho c v t2 [:= Y mid2 to] to2)
               (sametypeo c v X Y)
               (sameo c v mid1 mid2 X)))
       ([c v [:ind-= t m b] [[:apply mo to] t-o] [:ind-= t-o mo bo]]
        (fresh [from x X]
               (symbolo x)
               (syntho c v t [:= X from to] t-o)
               (isao c v [:Pi [[x X]] [:Pi [[t [:= X from x]]] :U]] mo)
               (isao c v b [[:apply mo from] [:same from]] bo)))

       ([c v [:ind-Either t m bl br] [mo to]
         [:ind-Either to mo blo bro]]
        (fresh [P S x]
               (syntho c v t [:Either P S] to)
               (isao c v m [:Pi [[x [:Either P S]]] :U] mo)
               (isao c v bl [:Pi [[x P]] [:apply mo [:left x]]] blo)
               (isao c v br [:Pi [[x S]] [:apply mo [:right x]]] bro)))

       ([c v :sole :Trivial :sole])

       ([c v [:ind-Absurd t m] mo [:ind-Absurd to mo]]
        (isao c v t :Absurd to)
        (typeo c v m mo))

       ([c v :Atom :U :Atom])
       ([c v [:Sig [[x A]] D] :U [:Sig [[x Ao]] Do]]
        (isao c v A :U Ao)
        (fresh [c2]
               (l/conso [x Ao] c c2)
               (isao c v D :U Do)))
       ([c v [:Sig args D] :U Do]
        (l/conde
          [(l/emptyo args)
           (syntho c v D :U Do)]
          [(fresh [arg rargs x A c2 Ao Do2]
                  (l/== Do [:Sig [[x Ao]] Do2])
                  (l/conso arg rargs args)
                  (l/== [x A] arg)
                  (l/conso [x Ao] c c2)
                  (l/conde
                    [(l/emptyo rargs)
                     (isao c2 v D :U Do2)]
                    [(isao c2 v [:Sig rargs D] :U Do2)]))]))
       ([c v [:Pair A D] :U [:Sig [[x Ao]] Do]]
        (fresh [x c2]
               (isao c v A :U Ao)
               (l/conso [x Ao] c c2)
               (isao c2 v D :U Do)))
       ([c v [:Pi [[x X]] R] :U [:Pi [[x Xo]] Ro]]
        (isao c v X :U Xo)
        (fresh [c2]
               (l/conso [x Xo] c c2)
               (isao c2 v R :U Ro)))
       ([c v
         [:Pi [[x X] . args] R]
         :U
         [:Pi [[x Xo]] Ro]]
        (isao c v X :U Xo)
        (fresh [c2]
               (l/conso [x Xo] c c2)
               (isao c2 v [:Pi args R] :U Ro)))
       ([c v [:-> X R] :U [:Pi [[x Xo]] Ro]]
        (isao c v X :U Xo)
        (fresh [x c2]
               (symbolo x)
               (l/conso [x Xo] c c2)
               (isao c2 v R :U Ro)))
       ([c v [:-> X . more] :U [:Pi [[x Xo]] Ro]]
        (isao c v X :U Xo)
        (fresh [x c2 Remtype]
               (symbolo x)
               (l/conso [x Xo] c c2)
               (l/conso :-> more Remtype)
               (isao c v Remtype :U Ro)))
       ([c v :Nat :U :Nat])
       ([c v [:List E] :U [:List E2]]
        (sameo c v E E2 :U))
       ([c v [:Vec E l] :U [:Vec Eo lo]]
        (isao c v E :U Eo)
        (isao c v l :Nat lo))
       ([c v [:= X from to] :U [:= Xo fromo too]]
        (isao c v X :U Xo)
        (isao c v from Xo fromo)
        (isao c v to Xo too))
       ([c v [:Either P S] :U [:Either Po So]]
        (isao c v P :U Po)
        (isao c v S :U So))
       ([c v :Trivial :U :Trivial])
       ([c v :Absurd :U :Absurd])

       ([c v [:the X einner] Xo eo]
        (typeo c v X Xo)
        (isao c v einner Xo eo))
       ([c v [:apply f arg]
         Rsub
         [:apply fo argo]]
        (fresh [x Arg R]
               (fresh [v2]
                      (l/conso [x argo] v v2)
                      (sametypeo c v2
                                 R
                                 Rsub))
               (syntho c v f [:Pi [[x Arg]] R] fo)
               (isao c v arg Arg argo)))
       ;; TODO decurrying sugar
       )

(defna dosameo [ac av ae ae2 aX]
       ([c v :zero :zero :Nat])
       ([c v :vecnil :vecnil [:Vec E :zero]])
       ([c v :Nat :Nat :U])
       ([c v :Trivial :Trivial :U])
       ([c v :Absurd :Absurd :U])

       ([c v [:ref e] [:ref e] X]                           ; implicit :ref handling
        (lookupo c e X))

       ([c v [:ref e] [:ref e2] X]
        (fresh [ev e2v]
               (lookupo v e ev)
               (lookupo v e e2v)
               (sameo c v ev e2v X))
        (lookupo c e X))

       ([c v [:ref e] e2 X]
        (lookupo v e e2)
        (lookupo c e X))

       ;; end refs

       ([c v x x :Atom]
        (symbolo x))

       ;; begin recursives

       ([c v [:cons a1 d1] [:cons a2 d2] [:Sig [[x A]] D]]
        (symbolo x)
        (sameo c v a1 a2 A)
        (sameo c v d1 d2 [:apply [:lam [x] D] a1]))
       ([c v [:car [:cons a1 d]] a2 A]
        (sameo c v a1 a2 A)
        (fresh [c2 x D]
               (symbolo x)
               (l/conso [x A] c c2)
               (sameo c2 v d d D)))
       ([c v [:car pr1] [:car pr2] A]
        (fresh [x D]
               (symbolo x)
               (sameo c v pr1 pr2 [:Sig [[x A]] D])))
       ([c v [:cdr pr1] [:cdr pr2] Dsub]
        (fresh [A D x]
               (symbolo x)
               (sametypeo c v Dsub [:apply [:lam [x] D] [:car pr1]])
               (sameo c v pr1 pr2 [:Sig [[x A]] D])))
       ([c v [:cdr [:cons a1 d1]] d2 Dsub]
        (fresh [A a2 c2 D x]
               (l/conso [x A] c c2)
               (symbolo x)
               (sametypeo c v Dsub [:apply [:lam [x] D] a2])
               (sameo c v a1 a2 A)
               (sameo c2 v
                      d1 d2 D)))

       ([c v [:lam [x] r1] [:lam [x] r2] [:Pi [[x Arg]] R]]
        (fresh [c2]
               (l/conso [x Arg] c c2)
               (sameo c2 v r1 r2 R)))

       ([c v [:add1 n1] [:add1 n2] :Nat]
        (sameo c v n1 n2 :Nat))

       ([c v
         [:whichNat t1 b1 s1]
         [:whichNat t2 b2 s2]
         B]
        (sameo c v t1 t2 :Nat)
        (fresh [bo]
               (syntho c v b1 B bo)
               (sameo c v bo b2 B))
        (fresh [x] (sameo c v s1 s2 [:Pi [[x :Nat]] B])))

       ([c v [:whichNat :zero
              b1                                            ; XXX the rules specify [the B b1] as the base val, but i'm not sure why we can't just synth B from b1
              s]
         b2 B]
        (fresh [b1o]
               (syntho c v b1 B b1o))
        (sameo c v b1 b2 B)
        (fresh [x] (sameo c v s s [:Pi [[x :Nat]] B])))
       ([c v
         [:whichNat [:add1 n1]
          b
          s1]
         [s2 n2]
         B]
        (sameo c v n1 n2 :Nat)
        (sameo c v b b B)
        (fresh [x]
               (sameo c v s1 s2 [:Pi [[x :Nat]] B])))
       ;; TODO finish Nat

       ;; TODO List

       ([c v [::vec e1 es1] [::vec e2 es2] [:Vec E [:add1 l]]]
        (sameo c v e1 e2 E)
        (sameo c v es1 es2 [:Vec E l]))
       ([c v [:head es1] [:head es2] E]
        (fresh [l]
               (sameo c v es1 es2 [:Vec E l])))
       ([c v [:head [::vec e1 es]] e2 E]
        (sameo c v e1 e2 E)
        (fresh [l]
               (sameo c v es es [:Vec E l])))
       ([c v [:tail es1] [:tail es2] [:Vec E l]]
        (sameo c v es1 es2 [:Vec E [:add1 l]]))
       ([c v [:tail [::vec e es1]] es2 [:Vec E l]]
        (sameo c v e e E)
        (sameo c v es1 es2 [:Vec E l]))
       ([c v [:ind-Vec l1 t1 m1 b1 s1] [:ind-Vec l2 t2 m2 b2 s2] [:apply [:apply m1 l1] t1]]
        (fresh [E]
               (sameo c v l1 l2 :Nat)
               (sameo c v t1 t2 [:Vec E l1])
               (sameo c v m1 m2 (u/ind-vec-motive E))
               (sameo c v b1 b2 [[:apply m1 :zero] :vecnil])
               (sameo c v s1 s2 (u/ind-vec-step m1 E))))
       ([c v [:ind-Vec :zero :vecnil m1 b1 s] b2 [:apply [:apply m2 :zero] :vecnil]]
        (fresh [E]
               (sameo c v b1 b2 [:apply [m1 :zero] :vecnil])
               (sameo c v s s (u/ind-vec-step m1 E))
               (sameo c v m1 m2 (u/ind-vec-motive E))))
       ([c v
         [:ind-Vec [:add1 l1] [::vec e1 es1] m1 b1 s1]
         [[[:apply [:apply s2 l2] e2] es2] [:ind-Vec l2 es2 m2 b2 s2]]
         [[:apply m2 [:add1 l1] [::vec e1 es1]]]]
        (fresh [E]
               (sameo c v l1 l2 :Nat)
               (sameo c v e1 e2 E)
               (sameo c v es1 es2 [:Vec E l1])
               (sameo c v m1 m2 (u/ind-vec-motive E))
               (sameo c v b1 b2 [:apply [:apply m1 :zero] :vecnil])
               (sameo c v s1 s2 (u/ind-vec-step m1 E))))

       ([c v [:same from] [:same to] [:= X from from]]
        (sameo c v from to X))
       ([c v [:replace t1 m1 b1] [:replace t2 m2 b2] [m1 to]]
        (fresh [from X]
               (sameo c v t1 t2 [:= X from to])
               (fresh [x]
                      (symbolo x)
                      (sameo c v m1 m2 [:Pi [[x X]] :U]))
               (sameo c v b1 b2 [m1 from])))
       ([c v [:replace [:same e] m b1] b2 [m e]]
        (fresh [X]
               (sameo c v e e X)
               (fresh [x]
                      (sameo c v m m [:Pi [[x X]] :U])))
        (sameo c v b1 b2 [m e]))
       ([c v [:cong X1 t1 f1] [:cong X2 t2 f2] [:= Y [:apply f1 from] [:apply f1 to]]]
        (sametypeo c v X1 X2)
        (fresh [x]
               (sameo c v f1 f2 [:Pi [[x X1]] Y]))
        (sameo c v t1 t2 [:= X1 from to]))
       ([c v [:cong X [:same e1] f1] [:same [:apply f2 e2]] [:= X [:apply f1 e1] [:apply f1 e1]]]
        (sameo c v e1 e2 X)
        (fresh [Y x]
               (sameo c v f1 f2 [:Pi [[x X]] Y])))
       ([c v [:symm t] [:symm t2] [:= X to from]]
        (sameo c v t t2 [:= X from to]))
       ([c v [:symm [:same e]] [:same e2] [:= X e e]]
        (sameo c v e e2 X))
       ([c v [:trans t t3] [:trans t2 t4] [:= X from to]]
        (fresh [mid]
               (sameo c v t t2 [:= X from mid])
               (sameo c v t3 t4 [:= X mid to])))
       ([c v [:trans [:same e] [:same e2]] [:same e3] [:= X e3 e3]]
        (sameo c v e e2 X)
        (sameo c v e2 e3 X))
       ([c v [:ind-= t1 m1 b1]
         [:ind-= t2 m2 b2]
         [:apply [:apply m1 to] t1]]
        (fresh [X from]
               (sameo c v t1 t2 [:= X from to])
               (fresh [x t]
                      (sameo c v m1 m2 [:Pi [[x X]] [:Pi [[t [:= X from x]]] :U]]))
               (sameo c v b1 b2 [:apply [:apply m1 from] [:same from]])))
       ([c v [:ind-= [:same e] m b1]
         b2 [:apply [:apply m e] [:same e]]]
        (fresh [X from]
               (sameo c v e e X)
               (fresh [x t]
                      (sameo c v m m [:Pi [[x X]] [:Pi [[t [:= X from x]]] :U]]))
               (sameo c v b1 b2 [:apply [:apply m from] [:same from]])))

       ([c v [:left lt1] [:left lt2] [:Either P S]]
        (sameo c v lt1 lt2 P))
       ([c v [:right rt1] [:right rt2] [:Either P S]]
        (sameo c v rt1 rt2 S))
       ([c v [:ind-Either t1 m1 bl1 br1]
         [:ind-Either t2 m2 bl2 br2]
         [:apply m t1]]
        (fresh [P S x]
               (symbolo x)
               (sameo c v t1 t2 [:Either P S])
               (sameo c v m1 m2 [:Pi [[x [:Either P S]]] :U])
               (sameo c v bl1 bl2 [:Pi [[x P]] [:apply m1 [:left x]]])
               (sameo c v br1 br2 [:Pi [[x S]] [:apply m1 [:right x]]])))
       ([c v [:ind-Either [:left lt1] m bl1 br]
         [bl2 lt2] [:apply m [:left lt1]]]
        (fresh [P S x]
               (sameo c v lt1 lt2 S)
               (sameo c v m m [:Pi [[x [:Either P S]]] :U])
               (sameo c v bl1 bl2 [:Pi [[x P]] [:apply m [:left x]]])
               (sameo c v br br [:Pi [[x S]] [:apply m [:right x]]])))
       ([c v [:ind-Either [:right rt1] m bl br1]
         [br2 rt2] [m [:right rt1]]]
        (fresh [P S x]
               (sameo c v rt1 rt2 S)
               (sameo c v m m [:Pi [[x [:Either P S]]] :U])
               (sameo c v bl bl [:Pi [[x P]] [:apply m [:left x]]])
               (sameo c v br1 br2 [:Pi [[x S]] [:apply m [:right x]]])))

       ([c v c1 :sole :Trivial]
        (sameo c v c1 c1 :Trivial))

       ([c v [:ind-Absurd t1 m1] [:ind-Absurd t2 m2] m1]
        (sameo c v t1 t2 :Absurd)
        (sameo c v m1 m2 :U))
       ([c v c1 c2 :Absurd]
        (sameo c v c1 c1 :Absurd)
        (sameo c v c2 c2 :Absurd))

       ([c v :Atom :Atom :U])
       ([c v [:Sig [[x A1]] D1] [:Sig [[x A2]] D2] :U]
        (sameo c v A1 D2 :U)
        (fresh [c2]
               (symbolo x)
               (l/conso [x A1] c c2)
               (sameo c2 v D1 D2 :U)))
       ([c v [:Pi [[x X1]] Y1] [:Pi [[x X2]] Y2] :U]
        (sameo c v X1 X2 :U)
        (fresh [c2]
               (symbolo x)
               (l/conso [x X1] c c2)
               (sameo c2 v Y1 Y2 :U)))
       ([c v [:List E1] [:List E2] :U]
        (sameo c v E1 E2 :U))
       ([c v [:Vec E1 l1] [:Vec E2 l2] :U]
        (sameo c v E1 E2 :U)
        (sameo c v l1 l2 :Nat))
       ([c v [:= X1 from1 to1] [:= X2 from2 to2] :U]
        (sameo c v X1 X2 :U)
        (sameo c v from1 from2 X1)
        (sameo c v to1 to2 X1))
       ([c v [:Either P1 S1] [:Either P2 S2] :U]
        (sameo c v P1 P2 :U)
        (sameo c v S1 S2 :U))
       ([c v p [:cons [:car p2] [:cdr p2]]
         [:Sig [[x ca]] cd]]
        (symbolo x)
        (sameo c v p p2 [:Sig [[x ca]] cd]))
       ([c v [:the X einner] e2 X]
        (sameo c v einner e2 X))
       ([c v f1 [:lam [x] [:apply f2 x]] [:Pi [[x Arg]] R]]
        (unboundo c x)
        (sameo c v f1 f2 [:Pi [[x Arg]] R]))

       ;; TODO should fn application be an explicit AST node?
       ;; otherwise matching cases like [[:ref a] arg] [:add1 :zero]
       ;; is a little tricky. seems like maybe we should retain :apply

       ;; generic application
       ([c v [:apply f1 arg1] [:apply f2 arg2] Rsub]
        (fresh [Arg R x]
               (sametypeo c v Rsub [:apply [:lam [x] R] arg1])
               (sameo c v f1 f2 [:Pi [[x Arg] R]])
               (sameo c v arg1 arg2 Arg)))
       ([c v
         [:apply f arg1]
         r2sub
         Rsub]
        (fresh [Arg R r2 c2 v2 x r1 arg2]
               (l/conso [x arg2] v v2)
               (l/conso [x Arg] c c2)
               (sametypeo c2 v2 R Rsub)
               (sameo c2 v2 r1 r2 R)
               (isao                                        ; TODO the rule doesn't specify value retrieval, but how else do we call functions by name at the syntax level? vaguely confused
                 c v f
                 [:Pi [[x Arg]] R]
                 [:lam [x] r1])
               (sameo c v arg1 arg2 Arg)
               (sameo c2 v2 r2 r2sub R))))

(defn sameo [c v e e2 X]
  (conda
    [(dosameo c v e e2 X)]
    [(dosameo c v e2 e X)]
    [(fresh [e3]
            (dosameo c v e e3 X)
            (dosameo c v e3 e2 X))]))

(defn type-of [c e]
  (first
    (run 1 [out]
         (typeo
           c [] e out))))

(defn check [c n e]
  (second (first
            (run 1 [t out]
                 (lookupo c n t)
                 (isao c [] e t out)))))

