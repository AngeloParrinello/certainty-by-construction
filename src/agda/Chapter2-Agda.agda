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

    module Sandbox-Usable where
        postulate
            Usable : Set
            Unusable : Set

        IsEven : ℕ → Set
        IsEven zero = Usable
        IsEven (suc zero) = Unusable
        IsEven (suc (suc n)) = IsEven n
    
    -- IsEven here is called an indexed type
    -- It is a type that depends on a value of another type, in this case ℕ
    data IsEven : ℕ → Set where
        -- base case: zero is even
        zero-even : IsEven zero
        -- inductive case: if n is even, then suc (suc n) is also even
        suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

    four-is-even : IsEven four
    -- do it via C-c C-r aka Refine, three times
    four-is-even = suc-suc-even (suc-suc-even zero-even)

    -- can we also prove that three is even?
    three-is-even : IsEven three
    -- it throws an error, because three is not even
    -- No introduction forms found
    three-is-even = suc-suc-even {!   !}    

    data IsOdd : ℕ → Set where
        -- base case: one is odd
        one-odd : IsOdd (suc zero)
        -- inductive case: if n is odd, then suc (suc n) is also odd
        suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

    -- inductive function to prove that every even number is followed by an odd number
    even-and-odd : {n : ℕ} → IsEven n → IsOdd (suc n)
    even-and-odd zero-even = one-odd
    even-and-odd (suc-suc-even n) = suc-suc-odd (even-and-odd n)