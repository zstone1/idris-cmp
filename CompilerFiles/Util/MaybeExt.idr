module MaybeExt
%access public export

getVal : (x : Maybe t) -> {auto prf : IsJust x} -> t
getVal {prf} Nothing = absurd prf
getVal {prf} (Just x) = x

