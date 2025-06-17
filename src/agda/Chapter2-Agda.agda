import Chapter1-Agda

module Chapter2-Agda where
    

module Definitions-Naturals where
    data ℕ : Set where
        zero : ℕ
        suc : ℕ → ℕ

module Sandbox-Naturals where
    open import Data.Nat
        using (ℕ; zero; suc)

    one : ℕ
    one = suc zero

    two : ℕ
    two = suc one

    three : ℕ
    three = suc two

    four : ℕ
    four = suc (suc (suc (suc zero)))

    open Chapter1-Agda
        using (Bool; false; true)

    n=0? : ℕ → Bool
    n=0? zero = true
    n=0? (suc n) = false

    n=2? : ℕ → Bool
    n=2? (suc (suc n)) = true
    n=2? _ = false
    

    even? : ℕ → Bool
    -- base case
    even? zero = true
    -- inductive case
    even? (suc zero) = false
    -- we subtract 2 from n, so we can use the same function
    -- technique called induction
    even? (suc (suc n)) = even? n
    
    data Evenℕ : Set where
        zero : Evenℕ
        suc-suc : Evenℕ → Evenℕ

    tonℕ : Evenℕ → ℕ
    tonℕ zero = zero
    tonℕ (suc-suc n) = suc (suc (tonℕ n))