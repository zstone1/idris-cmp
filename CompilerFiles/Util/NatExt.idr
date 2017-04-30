module NatExt
import Util.PreorderReasoningExt
import Data.Vect
import Data.Nat.DivMod
%access export

minusPlusCancel : (k : Nat) -> (n : Nat) -> {auto q: LTE n k} ->(k = (n +(k - n)))
minusPlusCancel k Z = rewrite minusZeroRight k in Refl
minusPlusCancel Z (S j) {q} = absurd q
minusPlusCancel (S k) (S j) {q} = cong $ minusPlusCancel k j {q = fromLteSucc q}

lteMinus : (m:Nat) ->(n :Nat) -> {auto q1 : LTE 1 n} -> {auto q2 : LTE n m} -> LT (m - n) m
lteMinus _ Z {q1} = absurd q1
lteMinus Z (S k) {q2} = absurd q2
lteMinus (S j) (S Z) = rewrite minusZeroRight j in (LTESucc lteRefl )
lteMinus (S k) (S(S j)) {q2} = let LTESucc f = q2 in
                                   LTESucc $ lteSuccLeft $ (lteMinus k (S j))

data NonZero : Nat -> Type where
  IsNotZero : NonZero (S k)

data GTE2 : Nat -> Type where
  MkGTE2 : GTE2 (S(S k))

lteOrGte : (a:Nat) -> (b:Nat) -> Either (a `LTE` b) (b `LTE` a)
lteOrGte Z b = Left LTEZero
lteOrGte a Z = Right LTEZero
lteOrGte (S a') (S b') with (lteOrGte a' b')
  | Left p = Left $ LTESucc p
  | Right p = Right $ LTESucc p

private
natToFin' : (x:Nat) -> (n:Nat) -> .(x `LT` n) -> Fin n
natToFin' _ Z p = absurd p
natToFin' Z (S k) p = FZ
natToFin' (S x) (S n) p = FS (natToFin' x n (fromLteSucc p))

private
natToFinToNat : finToNat (natToFin' x n l) = x
natToFinToNat {x = Z} {n=S k} = Refl
natToFinToNat {x = S x} {n = S n} {l = LTESucc l} = cong (natToFinToNat {x}{n}{l})
 
fromCoefficients : (base: Nat) -> List (Fin base) -> Nat
fromCoefficients b [] = 0
fromCoefficients b (x::xs) = finToNat x  + (fromCoefficients b xs) * b


data BaseB : (b:Nat) -> (n:Nat) -> Type where
  Coeffs : (l: List (Fin b)) -> BaseB b (fromCoefficients b l)

asBaseB : (predb:Nat) -> (n:Nat) -> BaseB (S predb) n
asBaseB _ Z = Coeffs []
asBaseB pb n with (n `divMod` pb) 
  asBaseB pb (r + q *(S pb)) | MkDivMod q r rLTb with (assert_total $ asBaseB pb q)
    asBaseB pb (r + (fromCoefficients (S pb) l) * (S pb)) | MkDivMod _ r rLTb | Coeffs l = 
          rewrite sym ( natToFinToNat {l=rLTb}) in Coeffs ((natToFin' r (S pb) rLTb) :: l) 
--total because (r+q*S(pb)) > 0. Could be argued by noting that 
--the whole recursion occurs at most n times, and counting down.

private
charMapping : List Char
charMapping = ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','g','h','i']

charToFin : Char ->  Maybe (Fin b) 
charToFin {b} x = do
   val <- findIndex ((== toLower x)) charMapping 
   natToFin val b

toNat : (base: Nat) -> String -> Maybe Nat
toNat b s = do
  let chars = reverse $ unpack s
  val <- traverse (charToFin ) chars
  pure $ fromCoefficients b val


fromNat : (base :Nat) -> {auto p : NonZero base} ->  Nat -> String
fromNat (S b) n with ( asBaseB b n)
  fromNat _ _ | Coeffs l = reverse $ pack $ map tochar l where
    tochar n = case index' (finToNat n) charMapping of
                    Just x => x
                    Nothing => believe_me "unbounded base doesn't make sense anyway"


hexString : Nat -> String 
hexString = ("0x"++) . fromNat 16






