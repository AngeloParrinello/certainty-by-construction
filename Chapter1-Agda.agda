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