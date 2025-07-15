module Chapter3-Proofs where

-- In Agda we use the Intuitionistic logic, so we can prove things by
-- constructing them, and we can prove things by contradiction, but we cannot
-- prove things by assuming the opposite and then deriving a contradiction.
-- So we break down the proofs in smaller steps, until we reach the
-- trivial case, which is the base case of the induction.
-- Intuitionistic proofs correspond to algorithms, so we can think of them as
-- programs that compute the proof.

-- Boolean blindness. In Agda we avoid it because we piggy back on the
-- type system the whole path that leads to the proof. 

open import Chapter1-Agda
  using (Bool; true; false; _∨_; _∧_; not)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_; _^_)

module Definition where
  infix 4 _≡_

  -- Here we take two parameters, the first one is the type of the elements we want to
  -- compare, and the second one is the type of the elements we want to compare.  But we 
  -- discard the second one, and we are saying that the only way to construct an equality
  -- is thorugh the fact that the two elements are the same, so we can
  -- construct a proof that they are equal.
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  -- Alternative implementation as in standard library

  -- data _≡_ {A : Set} (x : A) : A → Set where
    -- refl : x ≡ x

module Playground where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  _ : three ≡ suc (suc (suc zero))
  _ = refl

  _ : three ≡ two + one
  _ = refl

  -- Easy, depends on how the `_+_` has been defined
  zero-is-+-identity₁ : ∀ (n : ℕ) → zero + n ≡ n
  zero-is-+-identity₁ _ = refl

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- With flipped arguments requires more work, and the use of `cong`
  zero-is-+-identity : ∀ (n : ℕ) → n + zero ≡ n
  zero-is-+-identity zero = refl
  zero-is-+-identity (suc n) = cong suc (zero-is-+-identity n)

  suc-+ : ∀ (n m : ℕ) → n + suc m ≡ suc (n + m)
  suc-+ zero m = refl
  suc-+ (suc n) m = cong suc (suc-+ n m)

  zero-+ : ∀ (n : ℕ) → n + zero ≡ n
  zero-+ zero = refl
  zero-+ (suc n) = cong suc (zero-+ n)

  -- With `rewrite` we can rewrite the next goal using a function. Basically it
  -- means to use something already proven to change the goal or if you want to
  -- use a theorem to prove another
  commutativity-+ : ∀ (n m : ℕ) → n + m ≡ m + n
  -- originally the goal on the right is `m ≡ m + zero` since by pattern matching we know that n is zero
  -- using `zero-+` applied to m, we can rewrite the hole from `m ≡ m + zero` to `m ≡ m` which is trivially provable
  commutativity-+ zero m rewrite zero-+ m = refl
  -- originally the goal on the right is `suc n + m ≡ m + suc n`
  -- using `suc-+` applied to m and n we can rewrite the hole to `suc (n + m) ≡ suc (m + n)`
  -- which is exactly what we need for a recursive call using `cong`
  commutativity-+ (suc n) m  rewrite suc-+ m n = cong suc (commutativity-+ n m)

  -- We can also use the commutativity of the sum to prove the identity of zero
  zero-is-+-identity₂ : ∀ (n : ℕ) → n + zero ≡ n
  zero-is-+-identity₂ zero = refl
  zero-is-+-identity₂ (suc n) rewrite commutativity-+ n zero = refl

  +-identityˡ : ∀ (x : ℕ) → zero + x ≡ x
  +-identityˡ = zero-is-+-identity₁

  +-identityʳ : ∀ (x : ℕ) → x + zero ≡ x
  +-identityʳ = zero-is-+-identity

  -- Exercise
  *-identityˡ : ∀ (x : ℕ) → one * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (*-identityˡ x)

  -- Exercise
  *-identityʳ : ∀ (x : ℕ) → x * one ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  -- Exercise
  ^-identityʳ : ∀ (x : ℕ) → x ^ one ≡ x
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)

  -- Exercise
  ∧-identityˡ : ∀ (b : Bool) → true ∧ b ≡ b
  ∧-identityˡ _ = refl

  ∧-identityʳ : ∀ (b : Bool) → b ∧ true ≡ b
  ∧-identityʳ true = refl
  ∧-identityʳ false = refl

  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ _ = refl

  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl

  -- Exercise
  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ _ = refl

  -- Exercise
  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ false = refl
  ∧-zeroʳ true = refl

  -- Cannot do that
  -- *-identityˡ′ : ∀ (x : ℕ) → x ≡ one * x
  -- *-identityˡ′ = *-identityˡ

  -- Equality is simmetrical
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  -- Now we can do that
  *-identityˡ′ : ∀ (x : ℕ) → x ≡ one * x
  *-identityˡ′ x = sym (*-identityˡ x)

  -- For fun, is sym involutive?
  sym-involutive : {A : Set} → {x y : A} → (P : x ≡ y) → sym (sym P) ≡ P
  sym-involutive refl = refl

  -- Is not?
  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false = refl
  not-involutive true = refl

  -- Transitivity
  trans : {A : Set} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  trans refl refl = refl

  -- lets try to prove that a¹ = a + (b x 0)
  a^1≡a+b*0 : ∀ (a b : ℕ) → a ^ 1 ≡ a + (b * zero)
  a^1≡a+b*0 a b = trans (^-identityʳ a) (trans ( sym (+-identityʳ a)) (cong (λ φ → a + φ) ( sym (*-zeroʳ b))))
  -- shorter version
  -- a^1≡a+b*0 a b = trans (^-identityʳ a) (trans ( sym (+-identityʳ a)) (cong (a + _) ( sym (*-zeroʳ b))))

  -- factorial postfix notation
  _! : ℕ → ℕ
  zero ! = 1
  (suc n) ! = (suc n) * (n !)
  _ : 5 ! ≡ 120
  _ = refl

  ∣_ : ℕ → ℕ
  ∣_ = suc

  infix 20 ∣_

  five : ℕ
  -- five = suc (suc (suc (suc (suc zero))))
  --five = ∣ ∣ ∣ ∣ ∣ zero

  -- new syntax for zero
  ■ : ℕ
  ■ = zero

  five = ∣ ∣ ∣ ∣ ∣ ■

  -- delimited operators
  postulate
    ℝ : Set
    π : ℝ
    -- floor function
    ⌊_⌋ : ℝ → ℕ
    -- ceiling function
    ⌜_⌝ : ℝ → ℕ


  three' : ℕ
  three' = ⌊ π ⌋

  four' : ℕ
  four' = ⌜ π ⌝

  -- ternary operator
  _‽_⦂_ : {A : Set} → Bool → A → A → A
  false ‽ t ⦂ f = f
  true ‽ t ⦂ f = t

  infixr 20 _‽_⦂_

  _ : ℕ
  _ = not true ‽ 4 ⦂ 1

  -- let's define our if then else
  if_then_else_ : {A : Set} → Bool → A → A → A
  if_then_else_ = _‽_⦂_

  infixr 20 if_then_else_

  -- and use it
  _ : ℕ
  _ = if not true then 4 else 1

  -- due to our infixr defintion we can also nest it
  _ : ℕ
  _ = if not true then 4 else if true then 1 else 0

  -- case..of example (we do pattern matching on the right hand side)
  case_of_ : {A B : Set} → A → (A → B) → B
  case e of f = f e

  _ : ℕ
  _ = case true of λ 
      { true → 1
      ; false → 4
      }

  _is-equal-to_ : {A : Set} → A → A → Set
  x is-equal-to y = x ≡ y

  -- Equational Reasoning
  module ≡-Reasoning where
    
    -- tombstone marker formal proof ender, marks the end of the chain
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl
    infix 3 _∎

    -- we can use this to prove that two things are equal
    -- This style of proof is common in equational reasoning
    -- Each step should be definitionally equal
    -- It’s essentially syntax sugar that doesn’t change the proof content, just improves clarity
    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _ : 4 ≡ suc (one + two)
    _ = 
      4               ≡⟨⟩
      two + two       ≡⟨⟩
      suc one + two   ≡⟨⟩
      suc (one + two) ∎