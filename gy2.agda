module gy2 where

open import lib

id : Bool → Bool
id = λ x → x

t1 : Bool
t1 = true

not : Bool → Bool
not = λ x → if x then false else true

TT TF FT FF : Bool → Bool
TT = λ x → true
TF = λ x → if x then true else false -- =? id?
FT = λ x → if x then false else true
FF = λ x → if x then false else false

TT' : Bool → Bool
TT' = λ x → if true then true else false 

-- evaluate with C-c C-n

-- The only functions of type "Bool -> Bool" up to behaviour are id, not, T and F
-- Try to construct "g : (Bool -> Bool) -> Bool" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"

-- Functions with multiple arguments / Currying :
--   "Bool -> Bool -> Bool" = "Bool -> (Bool -> Bool)"

and or nand xor : Bool → Bool → Bool
and = λ a b → if a then b else false
or = λ a b → if a then true else b
nand = λ a b → if a then false else b
xor = λ a b → if a then (if b then false else true) else b
--xor = λ a b → if a then not b else b

-- Function as an argument
f : (Bool → Bool) → Bool
f = λ g → g false


---------------------------------------------------------
-- Natural numbers
---------------------------------------------------------

three = suc (suc (suc zero))

seventyseven : ℕ
seventyseven = 77

plus3 plus2 : ℕ → ℕ
plus3 = λ x → suc (suc (suc x))
plus2 = λ x → suc (suc x)

-- test it!

times2 times3 : ℕ → ℕ
times2 = λ n → primrec zero (λ _ fn' → suc (suc fn')) n
times3 = λ n → primrec zero (λ _ fn' → suc (suc (suc fn'))) n

-- test it!

-- prefix operator

_*2+2 : ℕ → ℕ
_*2+2 = λ n → primrec (suc (suc zero)) (λ _ fn' → suc (suc fn')) n

_*3+2 : ℕ → ℕ
_*3+2 = λ n → primrec 2 (λ _ fn' → (plus3 fn')) n


-- infix operator, fixity

-- infixl 4 _+_

_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec x (λ _ fn' → suc fn') y


-- test it e.g. (3 + 4) + 5 = 3 + (4 + 5)

-- requirements: isZero zero = true, otherwise: false
isZero : ℕ → Bool
isZero = λ x → primrec true (λ _ _ → false) x

-- requirements: pred 0 = 0, pred (1 + n) = n
pred : ℕ → ℕ
pred = λ x → primrec x (λ x' _ → x') x


even : ℕ → Bool
even = λ x → primrec true (λ x' fx' → (if fx' then false else true)) x

-- odd  : ℕ → Bool


-- product of two natural numbers
-- _*_ : ℕ → ℕ → ℕ
-- _*_ = λ x y → primrec zero (λ _ n → y + n) x

-- exponentiation of natural numbers
-- _^_ : ℕ → ℕ → ℕ

-- subtraction
-- _-_ : ℕ → ℕ → ℕ

-- equal? : ℕ → ℕ → Bool

-- _≥?_ : ℕ → ℕ → Bool

-- _>?_ : ℕ → ℕ → Bool




