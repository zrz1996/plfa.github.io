
module plfa.part1.Midterm where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
-- you can add any import definitions that you need
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _>_; z≤n; s≤s; _≤?_)
open import Data.Nat.Properties using (+-assoc; +-suc; *-suc; +-comm; *-distribˡ-+; *-identityʳ)
open import Relation.Nullary using (yes; no)
open import plfa.part1.Induction using (*-distrib-+; *-zero)
-- used for rewrite
simplify : ∀ {A : Set} (x : A) → x ≡ x
simplify x = refl

sum : ℕ → ℕ
sum 0 = 0
sum n@(suc sn) = sum sn + n

-- Problem 1
-- remove the "postulate" and prove this theorem, which is a version of
--   sum n ≡ n * (n + 1) / 2
---postulate
simple : ∀ (n : ℕ) → (sum n) * 2 ≡ (suc n) * n
simple zero = refl
simple (suc n) rewrite *-distrib-+ (sum n) (suc n) 2 
                | simple n 
                | simplify  n 
                | *-suc n n 
                | +-comm n (n * n)
                | sym (+-assoc n (n * n) n) 
                | +-comm n (n * n) | +-assoc (n * n) n n 
                | sym (+-suc (n * n)  (n + n)) | sym (+-assoc n (n * n) (suc (n + n))) 
                | +-comm n (n * n) 
                | sym (+-suc (n * n) n) 
                | +-assoc (n * n) n (suc (n + n)) 
                | sym (+-suc (n * n) (n + suc (n + n))) 
                | sym (+-suc n (suc (n + n))) 
                | sym (+-assoc (n * n) n (suc (suc (n + n)))) 
                | *-suc n 1 
                | *-identityʳ n = refl 


-- Problem 2
-- remove the postulate and implement this function, which gives an Natural
-- number approximation of square root
postulate 
  sqrt : ℕ → ℕ

-- you can run these test cases
-- _ : sqrt 0 ≡ 0
-- _ = refl
-- _ : sqrt 1 ≡ 1
-- _ = refl
-- _ : sqrt 2 ≡ 1
-- _ = refl
-- _ : sqrt 3 ≡ 1
-- _ = refl
-- _ : sqrt 4 ≡ 2
-- _ = refl
-- _ : sqrt 5 ≡ 2
-- _ = refl
-- _ : sqrt 6 ≡ 2
-- _ = refl
-- _ : sqrt 7 ≡ 2
-- _ = refl
-- _ : sqrt 8 ≡ 2
-- _ = refl
-- _ : sqrt 9 ≡ 3
-- _ = refl
-- _ : sqrt 10 ≡ 3
-- _ = refl
-- _ : sqrt 11 ≡ 3
-- _ = refl
-- _ : sqrt 12 ≡ 3
-- _ = refl
-- _ : sqrt 13 ≡ 3
-- _ = refl
-- _ : sqrt 14 ≡ 3
-- _ = refl
-- _ : sqrt 15 ≡ 3
-- _ = refl
-- _ : sqrt 16 ≡ 4
-- _ = refl
-- _ : sqrt 17 ≡ 4
-- _ = refl
-- _ : sqrt 18 ≡ 4
-- _ = refl
-- _ : sqrt 19 ≡ 4
-- _ = refl
-- _ : sqrt 20 ≡ 4
-- _ = refl
-- _ : sqrt 21 ≡ 4
-- _ = refl
-- _ : sqrt 22 ≡ 4
-- _ = refl
-- _ : sqrt 23 ≡ 4
-- _ = refl
-- _ : sqrt 24 ≡ 4
-- _ = refl
-- _ : sqrt 24 ≡ 4
-- _ = refl
-- _ : sqrt 24 ≡ 4
-- _ = refl
-- _ : sqrt 25 ≡ 5
-- _ = refl
-- _ : sqrt 26 ≡ 5
-- _ = refl
-- _ : sqrt 27 ≡ 5
-- _ = refl

