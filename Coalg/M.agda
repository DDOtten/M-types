{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    IsFinCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        Ty (ℓ-suc ℓ)
    IsFinCoalg M coiter = ∏[ C ∈ Coalg ] ∏[ f ∈ Mor C M ] f ≡ coiter C

    FinCoalg : Ty (ℓ-suc ℓ)
    FinCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        IsFinCoalg M coiter


    IsCohCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        Ty (ℓ-suc ℓ)
    IsCohCoalg M coiter =
        ∏[ C ∈ Coalg ] ∏[ f₁ ∈ Mor C M ] ∏[ f₂ ∈ Mor C M ]
        ∑[ p ∈ fun f₁ ≡ fun f₂ ] ∏[ c ∈ ty C ]
        ap (λ f → obs M (f c)) p · com {C} {M} f₂ c ≡
        com {C} {M} f₁ c · ap (λ f → P-fun f (obs C c)) p

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        IsCohCoalg M coiter


    IsTyBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        Ty (ℓ-suc ℓ)
    IsTyBisimCoalg M coiter =
        ∏[ ∼ ∈ TyBisim M ] ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ]
        (m₁ ⟨ M / ∼ ⟩ m₂ → m₁ ≡ m₂)

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        IsTyBisimCoalg M coiter


    IsFunBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        Ty (ℓ-suc ℓ)
    IsFunBisimCoalg M coiter =
        ∏[ ∼ ∈ FunBisim M ] ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ]
        (m₁ [ M / ∼ ] m₂ → m₁ ≡ m₂)

    FunBisimCoalg : Ty (ℓ-suc ℓ)
    FunBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ]
        IsFunBisimCoalg M coiter


    Coh→Fin : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsCohCoalg M coiter → IsFinCoalg M coiter
    Coh→Fin {M} {coiter} isCohCoalg = λ C → λ f →
        fin (isCohCoalg C f (coiter C))
        where
            fin : {C : Coalg} {f : Mor C M} →
                (
                    ∑[ p ∈ fun f ≡ fun (coiter C) ] ∏[ c ∈ ty C ]
                    ap (λ f → obs M (f c)) p · com {C} {M} (coiter C) c ≡
                    com {C} {M} f c · ap (λ f → P-fun f (obs C c)) p
                ) → (f ≡ coiter C)
            fin {C} {f} (refl , coh) =
                ≡-pair (
                    refl ,
                    funext (λ c →
                        (·-neutr₂ (com {C} {M} f c))⁻¹ ·
                        (coh c)⁻¹ ·
                        (·-neutr₁ (com {C} {M} (coiter C) c))
                    )
                )

    Fin→Coh : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsFinCoalg M coiter → IsCohCoalg M coiter
    Fin→Coh {M} {coiter} isFinCoalg = λ C → λ f₁ → λ f₂ →
        coh (isFinCoalg C f₁ · isFinCoalg C f₂ ⁻¹)
        where
            coh : {C : Coalg} {f₁ f₂ : Mor C M} →
                (f₁ ≡ f₂) → (
                    ∑[ p ∈ fun f₁ ≡ fun f₂ ] ∏[ c ∈ ty C ]
                    ap (λ f → obs M (f c)) p · com {C} {M} f₂ c ≡
                    com {C} {M} f₁ c · ap (λ f → P-fun f (obs C c)) p
                )
            coh {C} {f} {f} refl =
                (
                    refl ,
                    λ c →
                        ·-neutr₁ (com {C} {M} f c) ·
                        ·-neutr₂ (com {C} {M} f c)⁻¹
                )

    Fin→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsFinCoalg M coiter → IsTyBisimCoalg M coiter
    Fin→TyBisim {M} {coiter} isFinCoalg = λ ∼ → λ m₁ → λ m₂ → λ (s , p₁ , p₂) →
        p₁ ⁻¹ ·
        ≡-apply (ap pr₁ (
            isFinCoalg (coalg {M} ∼) (ρ₁ {M} ∼) ·
            isFinCoalg (coalg {M} ∼) (ρ₂ {M} ∼)⁻¹
        )) s ·
        p₂


    Coh→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsCohCoalg M coiter → IsTyBisimCoalg M coiter
    Coh→TyBisim {M} {coiter} isCohCoalg = λ ∼ → λ m₁ → λ m₂ → λ (s , p₁ , p₂) →
        p₁ ⁻¹ ·
        ≡-apply (pr₁ (isCohCoalg (coalg {M} ∼) (ρ₁ {M} ∼) (ρ₂ {M} ∼))) s ·
        p₂

    TyBisim→Coh : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsTyBisimCoalg M coiter → IsCohCoalg M coiter
    TyBisim→Coh {M} {coiter} isTyBisimCoalg = λ C → λ f₁ → λ f₂ →
        (
            funext (λ c →
                isTyBisimCoalg
                    (C , f₁ , f₂)
                    (fun f₁ c)
                    (fun f₂ c)
                    (c , refl , refl)
            ) ,
            {!   !}
        )

    TyBisim→FunBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisim→FunBisim {M} {coiter} isTyBisimCoalg = λ ∼ → λ m₁ → λ m₂ →
        isTyBisimCoalg (Fun→Ty {M} ∼) m₁ m₂ ∘ inv (Fun→Ty-pres {M} ∼ m₁ m₂)

    FunBisim→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    FunBisim→TyBisim {M} {coiter} isFunBisimCoalg = λ ∼ → λ m₁ → λ m₂ →
        isFunBisimCoalg (Ty→Fun {M} ∼) m₁ m₂
