{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Qplfa.Qpart1.Naturals where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name6 = "plfa.part1.Naturals.ℕ"
d6 = ()
data T6 = C8 | C10 Integer
name12 = "plfa.part1.Naturals.seven"
d12 :: Integer
d12 = coe (7 :: Integer)
name14 = "plfa.part1.Naturals._+_"
d14 = ((+) :: Integer -> Integer -> Integer)
name30 = "plfa.part1.Naturals._*_"
d30 = ((*) :: Integer -> Integer -> Integer)
name42 = "plfa.part1.Naturals._^_"
d42 :: Integer -> Integer -> Integer
d42 v0 v1
  = case coe v1 of
      0 -> coe (1 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe mulInt (coe v0) (coe d42 (coe v0) (coe v2))
name52 = "plfa.part1.Naturals._∸_"
d52 = ((\ x y -> max 0 (x - y)) :: Integer -> Integer -> Integer)
name70 = "plfa.part1.Naturals.Bin"
d70 = ()
data T70 = C72 | C74 T70 | C76 T70
name78 = "plfa.part1.Naturals.inc_"
d78 :: T70 -> T70
d78 v0
  = case coe v0 of
      C72 -> coe C76 (coe v0)
      C74 v1 -> coe C76 (coe v1)
      C76 v1 -> coe C74 (coe d78 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
name92 = "plfa.part1.Naturals.to_"
d92 :: Integer -> T70
d92 v0
  = case coe v0 of
      0 -> coe C74 (coe C72)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe d78 (coe d92 (coe v1))
name106 = "plfa.part1.Naturals.from_"
d106 :: T70 -> Integer
d106 v0
  = case coe v0 of
      C72 -> coe (0 :: Integer)
      C74 v1 -> coe mulInt (coe d106 (coe v1)) (coe (2 :: Integer))
      C76 v1
        -> coe
             addInt (coe (1 :: Integer))
             (coe mulInt (coe d106 (coe v1)) (coe (2 :: Integer)))
      _ -> MAlonzo.RTE.mazUnreachableError
