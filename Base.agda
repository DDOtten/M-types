{-# OPTIONS --without-K #-}


module M-types.Base where
    open import M-types.Ty public
    open import M-types.Equality public
    open import M-types.Sum public
    open import M-types.Product public


    id : {ℓ : Level} {X : Ty ℓ} →
        (X → X)
    id x = x

    _∘_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Ty ℓ₁} {Y : Ty ℓ₂} {Z : Ty ℓ₃} →
        (Y → Z) → (X → Y) → (X → Z)
    (g ∘ f) x = g (f x)


    tra : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {x₁ x₂ : X} →
        (Y : X → Ty ℓ₂) → x₁ ≡ x₂ → (Y x₁ → Y x₂)
    tra f refl = id

    ty = pr₁
    fun = pr₁
