{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Product where
    ∏ : {ℓ₁ ℓ₂ : Level} →
        (X : Ty ℓ₁) → (Y : X → Ty ℓ₂) → Ty (ℓ-max ℓ₁ ℓ₂)
    ∏ X Y = (x : X) → Y x

    ∏-syntax = ∏
    infix 2 ∏-syntax
    syntax ∏-syntax X (λ x → Y) = ∏[ x ∈ X ] Y
