{-# OPTIONS --without-K #-}


open import M-types.Ty
open import M-types.Sum
open import M-types.Prod
open import M-types.Eq


module M-types.Equi where
    Qinv : {X : Ty ℓ₁} {Y : Ty ℓ₂} →
        ∏[ f ∈ (X → Y)] Ty (ℓ-max ℓ₁ ℓ₂)
    Qinv {_} {_} {X} {Y} f = ∑[ g ∈ (Y → X) ]
        (∏[ x ∈ X ] g (f x) ≡ x) ×
        (∏[ y ∈ Y ] f (g y) ≡ y)

    IsEqui : {X : Ty ℓ₁} {Y : Ty ℓ₂} →
        ∏[ f ∈ (X → Y) ] Ty (ℓ-max ℓ₁ ℓ₂)
    IsEqui {_} {_} {X} {Y} f =
        (∑[ g ∈ (Y → X) ] ∏[ x ∈ X ] g (f x) ≡ x) ×
        (∑[ g ∈ (Y → X) ] ∏[ y ∈ Y ] f (g y) ≡ y)

    infix 8 _≃_
    _≃_ : ∏[ X ∈ Ty ℓ₁ ] ∏[ Y ∈ Ty ℓ₂ ] Ty (ℓ-max ℓ₁ ℓ₂)
    X ≃ Y = ∑[ f ∈ (X → Y) ] IsEqui f


    Qinv→IsEqui : {X : Ty ℓ₁} {Y : Ty ℓ₂} {f : X → Y} →
        Qinv f → IsEqui f
    Qinv→IsEqui (g , hom₁ , hom₂) = ((g , hom₁) , (g , hom₂))

    IsEqui→Qinv : {X : Ty ℓ₁} {Y : Ty ℓ₂} {f : X → Y} →
        IsEqui f → Qinv f
    IsEqui→Qinv {_} {_} {_} {_} {f} ((g₁ , hom₁) , (g₂ , hom₂)) =
        (
            g₁ ,
            hom₁ ,
            λ y → ap f (ap g₁ (hom₂ y)⁻¹ · hom₁ (g₂ y)) · hom₂ y
        )


    inv : {X : Ty ℓ₁} {Y : Ty ℓ₂} →
        ∏[ equi ∈ X ≃ Y ] (Y → X)
    inv (fun , isEqui) = pr₁ (IsEqui→Qinv isEqui)

    hom₁ : {X : Ty ℓ₁} {Y : Ty ℓ₂} →
        ∏[ equi ∈ X ≃ Y ] ∏[ x ∈ X ] inv equi (fun equi x) ≡ x
    hom₁ (fun , isEqui) = pr₁ (pr₂ (IsEqui→Qinv isEqui))

    hom₂ : {X : Ty ℓ₁} {Y : Ty ℓ₂} →
        ∏[ equi ∈ X ≃ Y ] ∏[ y ∈ Y ] fun equi (inv equi y) ≡ y
    hom₂ (fun , isEqui) = pr₂ (pr₂ (IsEqui→Qinv isEqui))
