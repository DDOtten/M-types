{-# OPTIONS --without-K #-}


open import M-types.Ty
open import M-types.Equality
open import M-types.Sum
open import M-types.Prod


module M-types.Equivalence where
    infix 8 _≃_
    _≃_ : {ℓ₁ ℓ₂ : Level} →
        ∏[ X ∈ Ty ℓ₁ ] ∏[ Y ∈ Ty ℓ₂ ] Ty (ℓ-max ℓ₁ ℓ₂)
    X ≃ Y = ∑[ f ∈ (X → Y) ]
        (∑[ f⁻¹ ∈ (Y → X) ] ∏[ x ∈ X ] f⁻¹ (f x) ≡ x) ×
        (∑[ f⁻¹ ∈ (Y → X) ] ∏[ y ∈ Y ] f (f⁻¹ y) ≡ y)
