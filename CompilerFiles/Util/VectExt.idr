module VectExt
import public Data.Vect
import Data.So
import MaybeExt
%access export

justMapMaybe : (f :t -> Maybe u) -> 
               (l : Vect k t) ->
               Elem x l ->
               IsJust (f x) -> 
               Elem (getVal $ f x) (snd $ mapMaybe f l)
justMapMaybe f [] elem p = absurd elem
justMapMaybe f (a :: as) Here isJust with (mapMaybe f as)
  | (len ** list) with (f a) 
    | Nothing = absurd isJust
    | Just y = Here
justMapMaybe {x} f (a :: as) (There later) isJust with ( justMapMaybe f as later isJust)
 | rec with (mapMaybe f as) proof p1
   | (len ** list) with ( f a )
      | Nothing = rec
      | Just y = There rec
 
filterForward : (Elem x l) -> (So (f x)) -> Elem x (snd $ filter f l)
filterForward {l=[]} elem _ = absurd elem 
filterForward {x=w} {l= w :: ws} {f} Here success with (filter f ws)
  | (l ** rest) with (f w)
    | False = absurd success 
    | True = Here
filterForward {x} {l=w :: ws} {f} (There later) success with (filterForward {x} {l=ws} {f} later success)
  | rec with (filter f ws)
    | (l ** rest) with (f w)
       | False = rec
       | True = There rec

filterBackwards : (l: Vect k t) -> Elem x (snd $ filter f l) -> (So (f x), Elem x l)
filterBackwards [] elem = absurd elem 
filterBackwards {x} {f} (w :: ws) elem with (filter f ws) proof p1
  |( _ ** rest) with (f w) proof p2
    filterBackwards {x}{f} (w::ws) elem | (_ ** rest) | False = 
      let (o, elemRec) = filterBackwards {x}{f} ws (rewrite sym p1 in elem) in
          (o, There elemRec)
 -- This line is the magic where idris has deduced out that the heads of both lists agree 
    filterBackwards {x} {f} (x :: ws) Here | (_ ** rest) | True = 
      (rewrite sym p2 in Oh, Here)
    filterBackwards {x} {f} (w :: ws) (There later) | (_ ** rest) | True =
      let (o, elemRec) = filterBackwards {x} {f} ws (rewrite sym p1 in later) in 
          (o, There elemRec)

