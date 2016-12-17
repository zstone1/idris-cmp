module BoolExt
import public Data.So

implementation Uninhabited (False = True) where
  uninhabited Refl impossible

