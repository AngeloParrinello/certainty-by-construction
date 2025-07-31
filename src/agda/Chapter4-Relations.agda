{-# OPTIONS --large-indices #-}

module Chapter4-Relations where

open import Chapter1-Agda
    using (Bool; false; true; not; _×_)

open import Chapter2-Numbers
    using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs

-- What is the type of Set itself? Set₁ !
_ : Set₁
_ = Set

-- and the type of Set₁ is Set₂, and so on
-- this collection of sets is an infinite hierarchy, and we refer to each as a sort or a universe

-- Agda and its Universe Polymorphism
open import Agda.Primitive
    using (Level; _⊔_; lzero; lsuc)

-- Let's test our new Level primitive
module Playground-Level where
    data Maybe₀ (A : Set) : Set where
        nothing₀ : Maybe₀ A
        just₀ : A → Maybe₀ A
    

    -- If we type ...
    -- _ = just₀ ℕ

    -- we get an error:
    -- Set₁ != Set
    -- when checking that the solution Set of metavariable _A_6 has the
    -- expected type Set

    -- We can generalize abstracting over the universe level
    data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
        just₁ : A → Maybe₁ A
        nothing₁ : Maybe₁ A

    _ = just₁ ℕ
    _ = just₁ 1

    -- private variable
    --    ℓ : Level

private variable
    ℓ ℓ₁ ℓ₂ a b c : Level
    A : Set a
    B : Set b
    C : Set c

-- Agda will implicitly infer the level ℓ
-- without us having to specify it
-- like we did above with {ℓ : Level}
data Maybe₂ (A : Set ℓ) : Set ℓ where
    just₂ : A → Maybe₂ A
    nothing₂ : Maybe₂ A

-- Set = Set lzero = Set₀
-- Set₁ = Set (lsuc lzero)

-- Max between two levels
-- _ : (lsuc lzero) ⊔ lzero ≡ lsuc lzero
-- _ = refl


module Definition-DependentPair where
    open Chapter3-Proofs

    record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
        constructor _,_
        field
            proj₁ : A
            proj₂ : B proj₁
    
    -- The following is the proof that there exists an `ℕ` so that its successor
    -- is `5` and we prove that by supplying the pair made of that particular `ℕ`
    -- and a function that describe that property.
    ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
    ∃n,n+1≡5 = 4 , PropEq.refl


open import Data.Product
  using (Σ; _,_)

module Sandbox-Relations where
    REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ (lsuc ℓ))
    REL A B ℓ = A → B → Set ℓ

    -- Functions as relations
    data _maps_↦_ (f : A → B) : REL A B lzero where
        app : {x : A} → f maps x ↦ f x

    _ : not maps true ↦ false
    _ = app

    _ : not maps false ↦ true
    _ = app

    -- Cannot evaluate `false` since is not related to `false` since `not` is involved
    -- _ : not maps false ↦ false

    Functional : REL A B ℓ → Set _
    Functional {A = A} {B = B} _~_
        = ∀ {x : A} {y z : B}
        → x ~ y → x ~ z
        → y ≡ z

    Total : REL A B ℓ → Set _
    Total {A = A} {B = B} _~_
        = ∀ (x : A) → Σ B (λ y → x ~ y)

    relToFn : (_~_ : REL A B ℓ) → Functional _~_ → Total _~_ → A → B
    relToFn _~_ _ total a = Σ.proj₁ (total a)

    -- Homogeneous relations
    Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
    Rel A ℓ = REL A A ℓ

    Reflexive : Rel A ℓ → Set _
    Reflexive {A = A} _~_ = ∀ {n : A} → n ~ n

    Symmetric : Rel A ℓ → Set _
    Symmetric {A = A} _~_ = ∀ {n m : A} → n ~ m → m ~ n

    Anti-Symmetric : Rel A ℓ → Set _
    Anti-Symmetric {A = A} _~_ = ∀ {n m : A} → n ~ m → m ~ n → n ≡ m

    Transitive : Rel A ℓ → Set _
    Transitive {A = A} _~_ = ∀ {n m p : A} → n ~ m → m ~ p → n ~ p





        

