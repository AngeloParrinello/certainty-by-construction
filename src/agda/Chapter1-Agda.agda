module Chapter1-Agda where
    -- This is a comment in Agda
    -- open import Data.Bool

    -- _ : Bool
    -- _ = false

    -- postulate
        -- Bool : Set
        -- false : Bool
        -- true : Bool
    
    data Bool : Set where
        false : Bool
        true : Bool
    
    not : Bool -> Bool
    not false = true
    not true = false

    open import Relation.Binary.PropositionalEquality
    _ : not(not false) ≡ false
    _ = refl

    -- or
    _v_ : Bool → Bool → Bool
    -- other in this case is a variable, often called bindings, because when we use it, we bind it to a value
    false v other = other
    true v other = true

    -- and
    _∧_ : Bool → Bool → Bool
    false ∧ other = false
    true ∧ other = other

    -- postulate always-stuck : Bool
    -- not always-stuck

module Example-Employees where
    open Booleans
    open import Data.String
        using (String)
    
    -- Employee data type, "one of" type
    data Department : Set where
        administrative : Department
        engineering : Department
        finance : Department
        marketing : Department
        sales : Department
    
    record Employee : Set where
        field
            name : String
            department : Department
            is-new-hire : Bool
    
    -- Example of an employee
    tillman : Employee
    tillman = record
        { name = "Tillman"
        ; department = engineering
        ; is-new-hire = true
        }




module Sandbox-Tuples where
    record _×_ (A : Set) (B : Set) : Set where
        field
            proj₁ : A
            proj₂ : B
        
    -- Example of a tuple
    open Booleans
    my-tuple : Bool × Bool
    my-tuple = record { proj₁ = true v true ; proj₂ = not true }

    -- first : Bool × Bool → Bool
    -- first record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁

    first : Bool × Bool → Bool
    first record { proj₁ = x } = x

    my-tuple-first : Bool
    my-tuple-first = my-tuple ._×_.proj₁

    my-tuple-second : Bool
    my-tuple-second = _×_.proj₂ my-tuple

    -- Every record creates a new modulo

    open _×_

    my-tuple-first : Bool
    my-tuple-first = my-tuple .proj₁

    -- every record field f of type F in record R gives rise to a function f : R → F
    -- so we can proj₂ on my-tuple
    my-tuple-second : Bool
    my-tuple-second = proj₂ my-tuple

    my-copattern : Bool × Bool
    proj₁ my-copattern = {! !}
    proj₂ my-copattern = {! !}

    -- copattern can be nested
    my-copattern-nested : Bool × (Bool × Bool)
    proj₁ my-copattern-nested = {! !}
    proj₁ (proj₂ my-copattern-nested) = {! !}
    proj₂ (proj₂ my-copattern-nested) = {! !}

    _,_ : {A, B : Set} → A → B → A × B
    x, x1 = record { proj₁ = x ; proj₂ = x1 }

    -- we can now rewrite my-tuple using the new notation
    my-tuple' : Bool × Bool
    my-tuple' = true, not true

module Sandbox-Tuples2 where
    open Booleans

    record _×_ (A : Set) (B : Set) : Set where
        constructor _,_  -- This is the constructor for the tuple
        field
            proj₁ : A
            proj₂ : B
    
    open _×_

    -- associativity right so true, false, true, false is the same as true, (false, (true, false))
    infixr 4 _,_
    infixr 2 _×_

    data _⊎_ (A : Set) (B : Set) : Set where
        inj₁ : A → A ⊎ B
        inj₂ : B → A ⊎ B
    infixr 1 _⊎_

    module Example-Pets where
        open import Data.String
            using (String)
        
        data Species : Set where
            bird cat dog reptile : Species

        data Temperament : Set where
            anxious chill excitable grumpy : Temperament
        
        record Pet : Set where
            constructor makePet
            field
                species : Species
                temperament : Temperament
                name : String
        
        makeGrumpyCat : String → Pet
        makeGrumpyCat name = makePet cat grumpy name

        -- but..
        makeGrumpyCat' : String → Pet
        makeGrumpyCat' = makePet cat grumpy

    or : Bool × Bool → Bool
    or (false, other) = other
    or (true, other) = true

    _ : Bool
    _ = or (true, false)

    curry : {A B C : Set} → (A × B → C) → A → B → C
    cury f a b = f (a, b)

    uncurry : {A B C : Set} → (A → B → C) → A × B → C
    uncurry f (a, b) = f a b

    -- really powerful...
    _ : Bool × Bool → Bool
    _ = uncurry _∨_

module Sandbox-Implicits where
    open import Data.Bool
        using (Bool; true; false; not; _∨_; _∧_)

    open import Data.Product
        using (_×_; proj₁; proj₂)

        renaming ( _,′_ to _,_ 
                ; curry′ to curry
                ; uncurry′ to uncurry
                )
    -- A, B are implicit arguments, completely optional and ignored
    mk-tuple : (A : Set) → (B : Set) → A → B → A × B
    mk-tuple A B x x1 = x, x1

    _ : Bool × Bool
    _ = mk-tuple Bool Bool true false

    data PrimaryColor : Set where
        red green blue : PrimaryColor

    -- does not work
    -- bad-tuple : Bool × Bool
    -- bad-tuple = mk-tuple PrimaryColor Bool true false

    -- and we can skip the types
    color-tuple : PrimaryColor × Bool
    color-tuple = mk-tuple _ _ red false

open import Data.Bool
    using (Bool; true; false; not; _∨_; _∧_)
    public

open import Data.Product
    using (_×_; proj₁; proj₂)
    public

open import Data.Sum
    using (_⊎_; inj₁; inj₂)
    public
