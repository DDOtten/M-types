{-# OPTIONS --without-K #-}

open import Agda.Primitive

module M-types.sum where
    infixr 4 _,_
    record ∑ {a b : Level} (X : Set a) (Y : X → Set b) : Set (a ⊔ b) where
        constructor _,_
        field
            pr₁ : X
            pr₂ : Y pr₁
    open ∑ public

    {-# BUILTIN SIGMA ∑ #-}

    ∑-syntax = ∑
    infix 2 ∑-syntax
    syntax ∑-syntax X (λ x → Y) = ∑[ x ∈ X ] Y

    infixr 2 _×_
    _×_ : {a b : Level} → (X : Set a) → (Y : Set b) → Set (a ⊔ b)
    X × Y = ∑[ x ∈ X ] Y
