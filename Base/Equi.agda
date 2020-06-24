{-# OPTIONS --without-K #-}


open import M-types.Base.Core
open import M-types.Base.Sum
open import M-types.Base.Prod
open import M-types.Base.Eq


module M-types.Base.Equi where
    Qinv : {X : Ty ℓ₀} {Y : Ty ℓ₁} →
        ∏[ f ∈ (X → Y)] Ty (ℓ-max ℓ₀ ℓ₁)
    Qinv {_} {_} {X} {Y} f = ∑[ g ∈ (Y → X) ]
        (∏[ x ∈ X ] g (f x) ≡ x) ×
        (∏[ y ∈ Y ] f (g y) ≡ y)

    IsEqui : {X : Ty ℓ₀} {Y : Ty ℓ₁} →
        ∏[ f ∈ (X → Y) ] Ty (ℓ-max ℓ₀ ℓ₁)
    IsEqui {_} {_} {X} {Y} f =
        (∑[ g ∈ (Y → X) ] ∏[ x ∈ X ] g (f x) ≡ x) ×
        (∑[ g ∈ (Y → X) ] ∏[ y ∈ Y ] f (g y) ≡ y)

    infixr 8 _≃_
    _≃_ : ∏[ X ∈ Ty ℓ₀ ] ∏[ Y ∈ Ty ℓ₁ ] Ty (ℓ-max ℓ₀ ℓ₁)
    X ≃ Y = ∑[ f ∈ (X → Y) ] IsEqui f


    Qinv→IsEqui : {X : Ty ℓ₀} {Y : Ty ℓ₁} {f : X → Y} →
        Qinv f → IsEqui f
    Qinv→IsEqui (g , hom₀ , hom₁) = ((g , hom₀) , (g , hom₁))

    IsEqui→Qinv : {X : Ty ℓ₀} {Y : Ty ℓ₁} {f : X → Y} →
        IsEqui f → Qinv f
    IsEqui→Qinv {_} {_} {_} {_} {f} ((g₀ , hom₀) , (g₁ , hom₁)) =
        (
            g₀ ,
            hom₀ ,
            λ y → ap f (ap g₀ (hom₁ y)⁻¹ · hom₀ (g₁ y)) · hom₁ y
        )


    inv : {X : Ty ℓ₀} {Y : Ty ℓ₁} →
        ∏[ equi ∈ X ≃ Y ] (Y → X)
    inv (fun , isEqui) = pr₀ (IsEqui→Qinv isEqui)

    hom₀ : {X : Ty ℓ₀} {Y : Ty ℓ₁} →
        ∏[ equi ∈ X ≃ Y ] ∏[ x ∈ X ] inv equi (fun equi x) ≡ x
    hom₀ (fun , isEqui) = pr₀ (pr₁ (IsEqui→Qinv isEqui))

    hom₁ : {X : Ty ℓ₀} {Y : Ty ℓ₁} →
        ∏[ equi ∈ X ≃ Y ] ∏[ y ∈ Y ] fun equi (inv equi y) ≡ y
    hom₁ (fun , isEqui) = pr₁ (pr₁ (IsEqui→Qinv isEqui))
