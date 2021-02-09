{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Relation.Binary.Morphism.Definitions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name20 = "Relation.Binary.Morphism.Definitions.Homomorphic₂"
d20 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d20 = erased
name32 = "Relation.Binary.Morphism.Definitions.Morphism"
d32 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  () -> MAlonzo.Code.Agda.Primitive.T14 -> () -> ()
d32 = erased
