{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Prod where
    ∏ : (X : Ty ℓ₀) → (Y : X → Ty ℓ₁) → Ty (ℓ-max ℓ₀ ℓ₁)
    ∏ X Y = (x : X) → Y x


    ∏-syntax : (X : Ty ℓ₀) → (Y : X → Ty ℓ₁) → Ty (ℓ-max ℓ₀ ℓ₁)
    ∏-syntax = ∏
    infix 2 ∏-syntax
    syntax ∏-syntax X (λ x → Y) = ∏[ x ∈ X ] Y


    id : {X : Ty ℓ} →
        (X → X)
    id = λ x → x

    infixr 9 _∘_
    _∘_ : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {Z : {x : X} → Y x → Ty ℓ₂} →
        ∏[ g ∈ ({x : X} → ∏[ y ∈ Y x ] Z y) ]
        ∏[ f ∈ (∏[ x ∈ X ] Y x) ]
        ∏[ x ∈ X ] Z (f x)
    f ∘ g = λ x → f (g x)
