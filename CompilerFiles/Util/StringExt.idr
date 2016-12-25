module StringExt
%access public export

pad : Char -> Nat -> String -> String
pad c n s = 
  case isLTE (length s) n of
       No _ => s
       Yes _ => pad' (n - (length s)) c s 
    where
    pad' : Nat -> Char -> String -> String
    pad' Z c s = s
    pad' (S k) c s = pad' k c (s ++ singleton c)


padSpace : Nat -> String -> String
padSpace = pad ' '









