module FizzBuzz where


    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
    open import Data.Empty using (⊥)
    open import Function.Base using (_∘_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
    open import Data.Product using (Σ; _,_; ∃; ∃-syntax)
    open import Relation.Nullary using (Dec; yes; no; ¬_)
    open import Data.String using (String)
    open import Data.Nat.Show using (show)
    open import Data.List using (List; []; _∷_; upTo; map)
    open import Data.Bool.Base using (Bool; true; false)

    -- FizzBuzz problem: given a list of natural numbers between 1 and `n`, for
    -- every number `i` in the list, print

    -- "FizzBuzz" if `i` is divisible by 3 and 5.
    -- "Fizz" if `i` is divisible by 3.
    -- "Buzz" if `i` is divisible by 5.
    -- The number itself as a string, if none of the previous conditions are true.

    -- You can create Fizzy if and only if the number is divisible by 3
    data Fizzy : ℕ → Set where
        base : Fizzy 0
        fizz : {n : ℕ} → Fizzy n → Fizzy (3 + n)
    
    _ : Fizzy 0
    _ = base

    -- This is a proof that demonstrates that Fizzy 1 is an empty type (has no constructors/inhabitants).
    -- The type signature: Fizzy 1 → ⊥ says we're constructing a function that takes a value of type
    -- Fizzy 1 and returns a value of type ⊥ (bottom/false). ⊥ is the empty type in Agda - it has no constructors,
    -- so no values can inhabit it.
    _ : Fizzy 1 → ⊥
    -- The implementation: λ () uses the "absurd pattern" or "absurd lambda" to indicate that
    -- there are no pattern to match on. This tells Agda "there are no constructors for the input type, so this case is impossible".
    _ = λ ()

    _ : Fizzy 3
    _ = fizz base

    _ : Fizzy 6
    _ = fizz (fizz base)

    -- You can create Buzzy if and only if the number is divisible by 5
    data Buzzy : ℕ → Set where
        base : Buzzy 0
        buzz : {n : ℕ} → Buzzy n → Buzzy (5 + n)

    _ : Buzzy 0
    _ = base

    _ : Buzzy 5
    _ = buzz base

    _ : Buzzy 10
    _ = buzz (buzz base)

    -- First step: let's prove that fizzy is true
    -- Prove that for every `n : ℕ` if it exists a `Fizzy n` then exists a `k : ℕ`
    -- such that `n ≡ k * 3` (which is to say that n is multiple of 3)
    -- It returns a dependent pair (a tuple with two values that are dependent)
    -- in this case: a natural number k (the quotient when dividing by 3)
    -- a proof that n ≡ k * 3
    fizzyOk : ∀ (n : ℕ) → Fizzy n → Σ ℕ (λ k → n ≡ k * 3)
    -- if n = 0, then k = 0 and the proof is trivial, refl proves that 0 ≡ 0 * 3
    fizzyOk zero x = (zero , refl)
    -- suc (suc (suc n)) matches numbers of the form n + 3
    -- (fizz x) matches the constructor that says "if n is fizzy, then n + 3 is also fizzy"
    -- in this case fizz x is the proof that the smaller number n is fizzy
    fizzyOk (suc (suc (suc n))) (fizz x) = 
        -- recursive call on fizzyOk, that gives us back k and p (the proof)
        let (k , p) = fizzyOk n x
        -- Remember that, the function cong (congruence) has type
        -- cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
        -- so this is what happens:
        -- We have p : n ≡ k * 3
        -- we apply cong (suc ∘ suc ∘ suc) to get:
        -- suc (suc (suc n)) ≡ suc (suc (suc (k * 3)))
        -- But suc (suc (suc (k * 3))) = k * 3 + 3 = (k + 1) * 3 = (suc k) * 3
        -- So we've proven that suc (suc (suc n)) ≡ (suc k) * 3
        in (suc k , cong (suc ∘ suc ∘ suc) p)

    -- Prove that Fizzy is decidable: for any `n : ℕ`, either construct a proof that
    -- n is divisible by 3 (with proof `p : Fizzy n`), or prove that it's not
    -- divisible by 3 (with proof `¬p : ¬ Fizzy n`)
    decFizzy : (n : ℕ) → Dec (Fizzy n)
    decFizzy zero = yes base
    decFizzy (suc zero) = no λ ()
    decFizzy (suc (suc zero)) = no λ ()
    decFizzy (suc (suc (suc n))) = {!   !}
