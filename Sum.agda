{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Sum  where
    infixr 4 _,_
    record ∑ (X : Ty ℓ₁) (Y : X → Ty ℓ₂) : Ty (ℓ-max ℓ₁ ℓ₂) where
        constructor _,_
        field
            pr₁ : X
            pr₂ : Y pr₁
    open ∑ public
    {-# BUILTIN SIGMA ∑ #-}


    ∑-syntax : (X : Ty ℓ₁) → (Y : X → Ty ℓ₂) → Ty (ℓ-max ℓ₁ ℓ₂)
    ∑-syntax = ∑
    infix 2 ∑-syntax
    syntax ∑-syntax X (λ x → Y) = ∑[ x ∈ X ] Y


    infixr 2 _×_
    _×_ : (X : Ty ℓ₁) → (Y : Ty ℓ₂) → Ty (ℓ-max ℓ₁ ℓ₂)
    X × Y = ∑[ x ∈ X ] Y


    ty = pr₁
    fun = pr₁
