{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Qplfa.Qpart1.Induction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

name14 = "plfa.part1.Induction.+-assoc"
d14 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d14 = erased
name30 = "plfa.part1.Induction.+-assoc-2"
d30 :: Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d30 = erased
name44 = "plfa.part1.Induction._.+-assoc-1"
d44 ::
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d44 = erased
name58 = "plfa.part1.Induction._._.+-assoc-0"
d58 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d58 = erased
name66 = "plfa.part1.Induction.+-identityʳ"
d66 :: Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d66 = erased
name74 = "plfa.part1.Induction.+-suc"
d74 :: Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d74 = erased
name86 = "plfa.part1.Induction.+-comm"
d86 :: Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d86 = erased
name102 = "plfa.part1.Induction.+-rearrange"
d102 ::
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d102 = erased
name120 = "plfa.part1.Induction.+-assoc′"
d120 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d120 = erased
name138 = "plfa.part1.Induction.+-identity′"
d138 :: Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d138 = erased
name150 = "plfa.part1.Induction.+-suc′"
d150 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d150 = erased
name166 = "plfa.part1.Induction.+-comm′"
d166 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d166 = erased
name192 = "plfa.part1.Induction.+-swap"
d192 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d192 = erased
name208 = "plfa.part1.Induction.*-distrib-+"
d208 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d208 = erased
name234 = "plfa.part1.Induction.*-assoc"
d234 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d234 = erased
name256 = "plfa.part1.Induction.*-zero"
d256 :: Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d256 = erased
name268 = "plfa.part1.Induction.*-suc"
d268 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d268 = erased
name296 = "plfa.part1.Induction.*-comm"
d296 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d296 = erased
name318 = "plfa.part1.Induction.0∸n≡0"
d318 :: Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d318 = erased
name328 = "plfa.part1.Induction.∸-|-assoc"
d328 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T12
d328 = erased
