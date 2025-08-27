module Double where

open import Data.Nat using (ℕ; zero; suc)

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))
