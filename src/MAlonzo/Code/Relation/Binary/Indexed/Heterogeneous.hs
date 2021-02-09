{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name8 = "Relation.Binary.Indexed.Heterogeneous.REL"
d8 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T14 -> ()
d8 = erased
name10 = "Relation.Binary.Indexed.Heterogeneous.Rel"
d10 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () -> (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T14 -> ()
d10 = erased
name12 = "Relation.Binary.Indexed.Heterogeneous.Setoid"
d12 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 -> ()
d12 = erased
name14 = "Relation.Binary.Indexed.Heterogeneous.IsEquivalence"
d14 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d14 = erased
