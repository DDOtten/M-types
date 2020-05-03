{-# OPTIONS --without-K #-}


open import M-types.Ty


module M-types.Equality where
    infix 4 _≡_
    data _≡_ {ℓ : Level} {X : Ty ℓ} : X → X → Ty ℓ where
        refl : {x : X} → x ≡ x
    open _≡_ public

    infix 10 _⁻¹
    _⁻¹ : {ℓ : Level} {X : Ty ℓ} {x₁ x₂ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₁
    refl ⁻¹ = refl

    infixr 9 _·_
    _·_ : {ℓ : Level} {X : Ty ℓ} {x₁ x₂ x₃ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
    refl · refl = refl
