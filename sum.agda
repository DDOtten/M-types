{-# OPTIONS --without-K #-}

module M-types.sum where
    open import Agda.Primitive

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

    _×_ : {a b : Level} → (X : Set a) → (Y : Set b) → Set (a ⊔ b)
    X × Y = ∑[ x ∈ X ] Y
