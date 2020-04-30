{-# OPTIONS --without-K #-}

open import M-types.ty

module M-types.equality where
    infix 4 _≡_
    data _≡_ {ℓ : Level} {X : Ty ℓ} : X → X → Ty ℓ where
        refl : {x : X} → x ≡ x
    open _≡_ public

    sym : {ℓ : Level} {X : Ty ℓ} {x₁ x₂ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₁
    sym refl = refl

    trans : {ℓ : Level} {X : Ty ℓ} {x₁ x₂ x₃ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
    trans refl refl = refl
