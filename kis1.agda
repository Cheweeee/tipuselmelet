{- BEGIN FIX-}
module kis1 where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

primrec : {A : Set}(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec u v zero = u
primrec u v (suc t) = v t (primrec u v t)

_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec x (λ y' x+y' → suc x+y') y

_*_ : ℕ → ℕ → ℕ
_*_ = λ x y → primrec zero (λ y' x*y' → x + x*y') y


-- exponentiation of natural numbers
-- 2 ^ 3 = 8
-- a ^ 0 = 1
_^_ : ℕ → ℕ → ℕ
{- END FIX-}

_^_ = λ x y → primrec (suc zero) (λ y' fy' → fy' * x) y 
