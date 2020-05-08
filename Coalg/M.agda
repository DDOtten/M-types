{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    FinCoalg : Ty (ℓ-suc ℓ)
    FinCoalg =
        ∑[ M ∈ Coalg ] ∏[ C ∈ Coalg ]
        ∑[ coiter ∈ Mor C M ] ∏[ f ∈ Mor C M ]
        f ≡ coiter

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg =
        ∑[ M ∈ Coalg ] ∏[ C ∈ Coalg ]
        ∑[ coiter ∈ Mor C M ] ∏[ f₁ ∈ Mor C M ] ∏[ f₂ ∈ Mor C M ]
        ∑[ α ∈ (∏[ c ∈ ty C ] fun f₁ c ≡ fun f₂ c) ] ∏[ c ∈ ty C ]
        ap (obs M) (α c) · (com {C} {M} f₂ c) ≡
        com {C} {M} f₁ c · ap (λ d → (pr₁ (obs C c) , d)) (funext (λ b → α (pr₂ (obs C c) b)))

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg =
        ∑[ M ∈ Coalg ] ∏[ C ∈ Coalg ]
        ∑[ coiter ∈ Mor C M ] ∏[ ∼ ∈ TyBisim M ]
        ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ] (m₁ ⟨ M / ∼ ⟩ m₂ → m₁ ≡ m₂)

    FunBisimCoalg : Ty (ℓ-suc ℓ)
    FunBisimCoalg =
        ∑[ M ∈ Coalg ] ∏[ C ∈ Coalg ]
        ∑[ coiter ∈ Mor C M ] ∏[ ∼ ∈ FunBisim M ]
        ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ] (m₁ [ M / ∼ ] m₂ → m₁ ≡ m₂)


    cohCoalgToTyBisimCoalg : CohCoalg → TyBisimCoalg
    cohCoalgToTyBisimCoalg (M , isCohCoalg) =
        (
            M ,
            λ C → (
                pr₁ (isCohCoalg C) ,
                λ ∼ → λ m₁ → λ m₂ → λ (s , p₁ , p₂) →
                    p₁ ⁻¹ · pr₁ (pr₂ (isCohCoalg (coalg {M} ∼)) (ρ₁ {M} ∼) (ρ₂ {M} ∼)) s · p₂
            )
        )

    tyBisimCoalgToFunBisimCoalg : TyBisimCoalg → FunBisimCoalg
    tyBisimCoalgToFunBisimCoalg (M , isTyBisimCoalg) =
        (
            M ,
            λ C → (
                pr₁ (isTyBisimCoalg C) ,
                λ ∼ → λ m₁ → λ m₂ →
                    pr₂ (isTyBisimCoalg C) (funToTy {M} ∼) m₁ m₂ ∘ inv (funToTyPres {M} ∼ m₁ m₂)
            )
        )
