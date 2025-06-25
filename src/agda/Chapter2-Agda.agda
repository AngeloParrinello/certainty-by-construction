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

    data Maybe (A : Set) : Set where
        just : A → Maybe A
        nothing : Maybe A

    evenEv : (n : ℕ) → Maybe (IsEven n)
    evenEv zero = just zero-even
    evenEv (suc zero) = nothing
    evenEv (suc (suc n)) with evenEv n
    ... | just x = just (suc-suc-even x)
    ... | nothing = nothing

    -- Addition
    _+_ : ℕ → ℕ → ℕ
    zero + y = y
    -- here the parenthesis are VERY important
    suc x + y = suc (x + y)
    infixl 6 _+_

    module Example-Silly where
        open Chapter1-Agda
            using (not)

        data ℕ' : Set where
            zero : ℕ'
            suc : ℕ' → ℕ'
            2suc : ℕ' → ℕ'

        -- silly example
        even?' : ℕ' → Bool
        even?' zero = true
        even?' (suc n) = not (even?' n)
        even?' (2suc zero) = true
        even?' (2suc n) = not (even?' n)

    _*_ : ℕ → ℕ → ℕ
    zero * b = zero
    suc a * b = b + (a * b)
    infixl 7 _*_

    _^_ : ℕ → ℕ → ℕ
    zero ^ _ = one
    suc a ^ b = a * (a ^ b)
    infixr 8 _^_

    _∸_ : ℕ → ℕ → ℕ
    zero ∸ _ = zero
    suc a ∸ zero = suc a
    suc a ∸ suc b = a ∸ b
    infixl 6 _∸_

    module Natural-Tests where
        open import Relation.Binary.PropositionalEquality
        
        _ : one + two ≡ three
        _ = refl

        _ : three ∸ one ≡ two
        _ = refl

        _ : one ∸ three ≡ zero
        _ = refl

        _ : one * two ≡ two
        _ = refl



module Misstep-Integers₁ where
    data ℤ : Set where
        zero : ℤ
        suc : ℤ → ℤ
        pred : ℤ → ℤ

module Misstep-Integers₂ where
    import Data.Nat as ℕ
    open ℕ using (ℕ; zero; suc)

    record ℤ : Set where
        constructor mkℤ
        field
            pos : ℕ
            neg : ℕ


    normalize : ℤ → ℤ
    normalize (mkℤ zero neg) = mkℤ zero neg
    normalize (mkℤ (suc pos) zero) = mkℤ (suc pos) zero
    normalize (mkℤ (suc pos) (suc neg)) = normalize (mkℤ pos neg)

    _+_ : ℤ → ℤ → ℤ
    mkℤ p₁ n₁ + mkℤ p₂ n₂ = normalize (mkℤ (p₁ ℕ.+ p₂) (n₁ ℕ.+ n₂))
    infixl 5 _+_

    _-_ : ℤ → ℤ → ℤ
    mkℤ p₁ n₁ - mkℤ p₂ n₂ =
        normalize (mkℤ (p₁ ℕ.+ n₂) (n₁ ℕ.+ p₂))
    infixl 5 _-_ 

    _*_ : ℤ → ℤ → ℤ
    mkℤ p₁ n₁ * mkℤ p₂ n₂ =
        normalize (mkℤ (p₁ ℕ.* p₂ ℕ.+ n₁ ℕ.* n₂) (p₁ ℕ.* n₂ ℕ.+ n₁ ℕ.* p₂))
    infixl 6 _*_

module Missstep-Integers₃ where
    open import Data.Nat

    data ℤ : Set where
        +_ : ℕ → ℤ
        -_ : ℕ → ℤ

    _ : ℤ
    _ = - 2

    _ : ℤ
    -- the space is necessary here
    _ = + 6


module Sandbox-Integers where
    import Data.Nat as ℕ
    open ℕ using (ℕ)

    data ℤ : Set where
        +_ : ℕ → ℤ
        -[1+_] : ℕ → ℤ

    0ℤ : ℤ
    0ℤ = + 0

    1ℤ : ℤ
    1ℤ = + 1

    suc : ℤ → ℤ
    suc (+ x) = + ℕ.suc x
    suc (-[1+ ℕ.zero ]) = 0ℤ
    suc (-[1+ ℕ.suc x ]) = -[1+ x ]

    pred : ℤ → ℤ
    pred (+ ℕ.zero) = -[1+ ℕ.zero ] -- check this one, should be just -1ℤ
    pred (+ ℕ.suc x) = + x
    pred (-[1+ x ]) = -[1+ ℕ.suc x ]

    pattern +[1+_] n = + ℕ.suc n
    pattern +0 = + ℕ.zero

    -_ : ℤ → ℤ
    - +0 = +0
    - +[1+ n ] = -[1+ n ]
    - -[1+ n ] = +[1+ n ]


    module Naive-Addition where
        _+_ : ℤ → ℤ → ℤ
        +0 + y = y
        +[1+ x ] + +0 = +[1+ x ]
        +[1+ x ] + +[1+ y ] = +[1+ 1 ℕ.+ x ℕ.+ y ]
        +[1+ x ] + -[1+ y ] = {!   !}
        -[1+ x ] + +0 = -[1+ x ]
        -[1+ x ] + +[1+ y ] = {!   !}
        -[1+ x ] + -[1+ y ] = -[1+ 1 ℕ.+ x ℕ.+ y ]

    _⊖_ : ℕ → ℕ → ℤ
    ℕ.zero ⊖ ℕ.zero = +0
    ℕ.zero ⊖ ℕ.suc n = -[1+ n ]
    ℕ.suc n ⊖ ℕ.zero = +[1+ n ]
    ℕ.suc n ⊖ ℕ.suc m = n ⊖ m

    infixl 5 _+_

    _+_ : ℤ → ℤ → ℤ
    + x + + y = +(x ℕ.+ y)
    + x + -[1+ y ] = x ⊖ ℕ.suc y
    -[1+ x ] + + y = y ⊖ ℕ.suc x
    -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

    infixl 5 _-_
    _-_ : ℤ → ℤ → ℤ
    x - y = x + - y

    infixl 6 _*_
    _*_ : ℤ → ℤ → ℤ
    x * +0 = +0
    x * +[1+ ℕ.zero ] = x
    x * -[1+ ℕ.zero ] = - x
    x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
    x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x

    module Tests where
        open import Relation.Binary.PropositionalEquality

        _ : -(+ 2) * - (+ 6) ≡ + 12
        _ = refl

        _ : (+ 3) - (+ 10) ≡ -(+ 7)
        _ = refl

open import Data.Nat
    using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
    public

open Sandbox-Naturals
    using (one; two; three; four)
    public

open Sandbox-Naturals
    using (IsEven)
    renaming ( zero-even to zero-even
            ; suc-suc-even to ss-even
            )
    public

open import Data.Maybe
    using (Maybe; just; nothing)
    public




