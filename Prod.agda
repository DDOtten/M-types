{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Prod where
    ∏ : (X : Ty ℓ₁) → (Y : X → Ty ℓ₂) → Ty (ℓ-max ℓ₁ ℓ₂)
    ∏ X Y = (x : X) → Y x


    ∏-syntax : (X : Ty ℓ₁) → (Y : X → Ty ℓ₂) → Ty (ℓ-max ℓ₁ ℓ₂)
    ∏-syntax = ∏
    infix 2 ∏-syntax
    syntax ∏-syntax X (λ x → Y) = ∏[ x ∈ X ] Y


    id : {X : Ty ℓ₁} →
        (X → X)
    id = λ x → x

    infixr 9 _∘_
    _∘_ : {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {Z : {x : X} → Y x → Ty ℓ₃} →
        ∏[ g ∈ ({x : X} → ∏[ y ∈ Y x ] Z y) ]
        ∏[ f ∈ (∏[ x ∈ X ] Y x) ]
        ∏[ x ∈ X ] Z (f x)
    f ∘ g = λ x → f (g x)
