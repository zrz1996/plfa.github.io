{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

name24 = "Relation.Binary.Indexed.Heterogeneous.Core.IREL"
d24 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T14 -> ()
d24 = erased
name44 = "Relation.Binary.Indexed.Heterogeneous.Core.IRel"
d44 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () -> (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T14 -> ()
d44 = erased
name64 = "Relation.Binary.Indexed.Heterogeneous.Core._=[_]⇒_"
d64 ::
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  MAlonzo.Code.Agda.Primitive.T14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d64 = erased
