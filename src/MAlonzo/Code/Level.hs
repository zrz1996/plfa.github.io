{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Level where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name8 = "Level.Lift"
d8 a0 a1 a2 = ()
newtype T8 = C20 AgdaAny
name18 = "Level.Lift.lower"
d18 :: T8 -> AgdaAny
d18 v0
  = case coe v0 of
      C20 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name22 = "Level.0ℓ"
d22 :: MAlonzo.Code.Agda.Primitive.T14
d22 = coe MAlonzo.Code.Agda.Primitive.d16
name26 = "Level.levelOfType"
d26 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  () -> MAlonzo.Code.Agda.Primitive.T14
d26 v0 v1 = du26 v0
du26 ::
  MAlonzo.Code.Agda.Primitive.T14 -> MAlonzo.Code.Agda.Primitive.T14
du26 v0 = coe v0
name34 = "Level.levelOfTerm"
d34 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Primitive.T14
d34 v0 v1 v2 = du34 v0
du34 ::
  MAlonzo.Code.Agda.Primitive.T14 -> MAlonzo.Code.Agda.Primitive.T14
du34 v0 = coe v0
