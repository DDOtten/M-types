{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Sum  where
    infixr 4 _,_
    record ∑ (X : Ty ℓ₀) (Y : X → Ty ℓ₁) : Ty (ℓ-max ℓ₀ ℓ₁) where
        constructor _,_
        field
            pr₀ : X
            pr₁ : Y pr₀
    open ∑ public
    {-# BUILTIN SIGMA ∑ #-}


    ∑-syntax : (X : Ty ℓ₀) → (Y : X → Ty ℓ₁) → Ty (ℓ-max ℓ₀ ℓ₁)
    ∑-syntax = ∑
    infix 2 ∑-syntax
    syntax ∑-syntax X (λ x → Y) = ∑[ x ∈ X ] Y


    infixr 2 _×_
    _×_ : (X : Ty ℓ₀) → (Y : Ty ℓ₁) → Ty (ℓ-max ℓ₀ ℓ₁)
    X × Y = ∑[ x ∈ X ] Y


    ty = pr₀
    fun = pr₀
