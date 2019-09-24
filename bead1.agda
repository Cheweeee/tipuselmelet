{- BEGIN FIX -}
module bead1 where

infixl 3 _≡_
infixl 4 _+_
infixl 5 _*_

data Bool : Set where
  false : Bool
  true : Bool

if_then_else_ : {A : Set}(t : Bool)(u v : A) → A
if true then u else v = u
if false then u else v = v

not : Bool → Bool
not = λ b → if b then false else true

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

primrec : {A : Set}(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec u v zero = u
primrec u v (suc t) = v t (primrec u v t)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- requirements: odd 0 = false, odd 1 = true, ...
odd : ℕ → Bool

{- END FIX -}
-- Implement your solution here!

odd = λ x → primrec false (λ x' fx' → (not fx')) x

{- BEGIN FIX -}
test-odd1 : odd 3 ≡ true
test-odd2 : odd 0 ≡ false
test-odd3 : odd 1 ≡ true
test-odd4 : odd 1001 ≡ true
{- END FIX -}
-- Test your solution here by uncommenting the lines:
test-odd1 = refl
test-odd2 = refl
test-odd3 = refl
test-odd4 = refl

{- BEGIN FIX -}
-- sum n is the sum of the natural numbers from 0 to n.
-- sum 0 = 0, sum 1 = 1, sum 2 = 3, sum 3 = 6, sum 4 = 10, ...
sum : ℕ → ℕ

{- END FIX -}
-- Implement your solution here!
sum = λ x → primrec x (λ x' fx' → x' + fx') x

{- BEGIN FIX -}
test-sum1 : sum 0 ≡ 0
test-sum2 : sum 1 ≡ 1
test-sum3 : sum 3 ≡ 6
test-sum4 : sum 9 ≡ 45
{- END FIX -}
-- Test your solution here by uncommenting the lines:
test-sum1 = refl
test-sum2 = refl
test-sum3 = refl
test-sum4 = refl

{- BEGIN FIX -}
-- product of two natural numbers
_*_ a b : ℕ → ℕ → ℕ

{- END FIX -}
-- Implement your solution here!
isZero : ℕ → Bool
isZero = λ x → primrec true (λ _ _ → false) x

_*_ = λ a b → if (isZero b) then zero else (primrec zero (λ _ fa' → fa' + b) a)

{- BEGIN FIX -}
test-*1 : ∀ a → a * 0 ≡ 0
test-*2 : 1 * 3 ≡ 3
test-*3 : 9 * 4 ≡ 36
test-*4 : 7 * 11 ≡ 77
{- END FIX -}
-- Test your solution here by uncommenting the lines:
test-*1 = λ n → refl
test-*2 = refl
test-*3 = refl
test-*4 = refl

t : ℕ → ℕ
t =  λ x → primrec (suc (suc (suc zero))) (λ _ n → suc (suc n)) x

a = λ x y → x
b = λ y x → x
f : Bool → ℕ
f = λ x → if x then zero else (suc (suc zero))

f1 f2 : ℕ → ℕ → ℕ
f1 = λ x y → x
f2 = λ y x → y

test1 : f1 ≡ f2
test1 = refl 
