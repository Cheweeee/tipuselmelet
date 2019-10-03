module gy4 where

open import lib

infixl 3 _≡_

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

isZero : ℕ → Bool
isZero = λ n → primrec true (λ _ _ → false) n

-- HW1
-- x >₁ y returns true if x = suc y
-- implement it without pattern matching based on the equation implementation from the tutorial (double primrec)
_>₁_ : ℕ → ℕ → Bool
_>₁_ = λ x → primrec (λ _ → false) (λ x' eq' y → primrec true (λ y' _ → eq' y' ) y ) x

-- HW2
-- isOne 0 = false, isOne 1 = true, isOne 2 = false, isOne 3 = false, ...
-- You can use isZero function here. 
isOne : ℕ → Bool
isOne = λ x → primrec false (λ x' _ → isZero x') x

-- HW3
-- x <₁ y returns true if x = suc y
-- Same as above at _>₁_
_<₁_ : ℕ → ℕ → Bool
_<₁_ = λ x → primrec (isOne) (λ x' eq' y → primrec (false) (λ y' _ → eq' y' ) y) x

{-
-- This part is to test the implementation
test10 : 0 >₁ 2 ≡ false
test10 = refl
test11 : 1 >₁ 2 ≡ false
test11 = refl
test12 : 2 >₁ 2 ≡ false
test12 = refl
test13 : 3 >₁ 2 ≡ true
test13 = refl
test14 : 4 >₁ 2 ≡ false
test14 = refl

test20 : isOne 0 ≡ false
test20 = refl
test21 : isOne 1 ≡ true
test21 = refl
test22 : isOne 2 ≡ false
test22 = refl
test23 : isOne 3 ≡ false
test23 = refl

test30 : 0 <₁ 2 ≡ false
test30 = refl
test31 : 1 <₁ 2 ≡ true
test31 = refl
test32 : 2 <₁ 2 ≡ false
test32 = refl
-}


---------------------------------------------------------
-- Descartes product
---------------------------------------------------------
-- define all the elements of Bool × Bool!
p1 p2 p3 p4 p5 : Bool × Bool
p1 = true , true
p2 = true , false
p3 = false , true
p4 = false , false

p5 = true , true

and : Bool → Bool → Bool
and = λ x y → if x then y else false

uncurryBool : (Bool → Bool → Bool) → Bool × Bool → Bool
uncurryBool = λ f → (λ pr → f (proj₁ pr) (proj₂ pr) )

swapBool : Bool × Bool → Bool × Bool
swapBool = λ p → proj₂ p , proj₁ p
-- swap (u , v) = (v , u) for any u, b

apply : (Bool → Bool) × Bool → Bool
apply = λ f → proj₁ f (proj₂ f)
-- apply (f , u) = f u

---------------------------------------------------------
-- Abstract types
---------------------------------------------------------

idX     : X → X
idX = λ x → x

pick    : X → X → X
pick = λ x y → y
pick*   : X → (X → X) → X
pick* = λ x id → x
pick?   : (X → X) → X
pick? = λ f → {!!} --ilyen fv nincs

swap    : X × Y → Y × X
swap = λ x  → proj₂ x , proj₁ x

curry   : (X × Y → Z) → (X → Y → Z)
curry = λ f → (λ x y → f (x , y))

uncurry : (X → Y → Z) → (X × Y → Z)
uncurry = λ f → (λ x  → f (proj₁ x) (proj₂ x))

assoc   : (X × Y) × Z → X × (Y × Z)
assoc = λ p → proj₁ (proj₁ p) , (proj₂ (proj₁ p) , proj₂ p)

diag    : X → X × X
diag = λ x → x , x

_∘_     : (Y → Z) → (X → Y) → (X → Z)
_∘_ = λ f g → λ x → f (g x)



---------------------------------------------------------
-- Empty type
---------------------------------------------------------

magicZ : (X → ⊥) → X → Z
magicZ = λ f x → exfalso (f x)
magicY : (X → ⊥) → X → Y
magicY = λ f x → exfalso (f x)


---------------------------------------------------------
-- Unit type
---------------------------------------------------------

interesting   : ⊥ → X
interesting = λ a → exfalso a
uninteresting : X → ⊤
uninteresting = λ _ → tt

---------------------------------------------------------
-- Abbreviated types
---------------------------------------------------------

currying : (X → Y → Z) ↔ (X × Y → Z) -- A ↔ B az (A → B , B → A)
currying = uncurry , curry

→×distr-r : (X → Y) × (X → Z) → (X → Y × Z)
→×distr-r = {!!}

→×distr-l : (X → Y × Z) → (X → Y) × (X → Z)
→×distr-l = {!!}

→×distr : (X → Y) × (X → Z) ↔ (X → Y × Z)
→×distr = {!!}

---------------------------------------------------------
-- Coproducts
---------------------------------------------------------

-- how many implementations?
undiag : X ⊎ X → X
undiag = {!!}

×⊎distr : (X × Y) ⊎ Z → (X ⊎ Z) × (Y ⊎ Z)
×⊎distr = {!!}


{-
---------------------------------------------------------
-- Algebraic structure on types
---------------------------------------------------------

-- some of the following laws hold up to definitional isomorphism, not
-- only logical equivalence. We can test these in Agda by normalising
-- λ x → proj₁ ⊎ass (proj₂ ⊎ass x) etc.

-- ⊎ is a commutative monoid

⊎ass  : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
⊎ass = {!!}
⊎lid  : ⊥ ⊎ X ↔ X
⊎lid = {!!}
⊎rid  : X ⊎ ⊥ ↔ X
⊎rid = {!!}
⊎comm : (X ⊎ Y) ↔ Y ⊎ X
⊎comm = {!!}
-- × is a commutative monoid with a null element

×ass  : (X × Y) × Z ↔ X × (Y × Z)
×ass = {!!}
×lid  : ⊤ × X ↔ X
×lid = {!!}
×rid  : X × ⊤ ↔ X
×rid = {!!}
×comm : (X × Y) ↔ Y × X
×comm = {!!}
×null : ⊥ × X ↔ ⊥
×null = {!!}
-- →

→lid : ⊤ → X ↔ X
→lid = {!!} 
→rnull : X → ⊤ ↔ ⊤
→rnull = {!!}
→⊥⊤ : ⊥ → X ↔ ⊤
→⊥⊤ = {!!} 
-- distributivity laws

⊎×dist : (X ⊎ Y) × Z ↔ (X × Z) ⊎ (Y × Z)
⊎×dist = {!!}
×⊎dist : (X × Y) ⊎ Z ↔ (X ⊎ Z) × (Y ⊎ Z) -- this is not an isomorphism
×⊎dist = {!!}
⊎→dist : (X ⊎ Y) → Z ↔ (X → Z) × (Y → Z)
⊎→dist = {!!}
→×dist : X → (Y × Z) ↔ (X → Y) × (X → Z)
→×dist = {!!}
×→dist : (X × Y) → Z ↔ X → (Y → Z)
×→dist = {!!}
-}
