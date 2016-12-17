module MaybeExt
%access public export
Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

getVal : (x : Maybe t) -> {auto prf : IsJust x} -> t
getVal {prf} Nothing = absurd prf
getVal {prf} (Just x) = x

