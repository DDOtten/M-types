{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    IsFinCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] Ty (ℓ-suc ℓ)
    IsFinCoalg M coiter = ∏[ C ∈ Coalg ] ∏[ f ∈ Mor C M ] f ≡ coiter C

    FinCoalg : Ty (ℓ-suc ℓ)
    FinCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] IsFinCoalg M coiter


    IsCohCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] Ty (ℓ-suc ℓ)
    IsCohCoalg M coiter =
        ∏[ C ∈ Coalg ] ∏[ f₁ ∈ Mor C M ] ∏[ f₂ ∈ Mor C M ]
        ∑[ hom ∈ (∏[ c ∈ ty C ] fun f₁ c ≡ fun f₂ c) ] ∏[ c ∈ ty C ]
        ap (obs M) (hom c) · (com {C} {M} f₂ c) ≡
        com {C} {M} f₁ c · ap (λ d → (pr₁ (obs C c) , d)) (inv (≡-apply , funext) (λ b → hom (pr₂ (obs C c) b)))

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] IsCohCoalg M coiter


    IsTyBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] Ty (ℓ-suc ℓ)
    IsTyBisimCoalg M coiter = ∏[ ∼ ∈ TyBisim M ] ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ] (m₁ ⟨ M / ∼ ⟩ m₂ → m₁ ≡ m₂)

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] IsTyBisimCoalg M coiter


    IsFunBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] Ty (ℓ-suc ℓ)
    IsFunBisimCoalg M coiter = ∏[ ∼ ∈ FunBisim M ] ∏[ m₁ ∈ ty M ] ∏[ m₂ ∈ ty M ] (m₁ [ M / ∼ ] m₂ → m₁ ≡ m₂)

    FunBisimCoalg : Ty (ℓ-suc ℓ)
    FunBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] Mor C M) ] IsFunBisimCoalg M coiter


    Coh→Fin : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsCohCoalg M coiter → IsFinCoalg M coiter
    Coh→Fin {M} {coiter} isCohCoalg = λ C → λ f → {!  !}
        where
            fin : {C : Coalg} {f : Mor C M} →
                (
                    ∑[ hom ∈ (∏[ c ∈ ty C ] fun f c ≡ fun (coiter C) c) ] ∏[ c ∈ ty C ]
                    ap (obs M) (hom c) · (com {C} {M} (coiter C) c) ≡
                    com {C} {M} f c · ap (λ d → (pr₁ (obs C c) , d)) (inv (≡-apply , funext) (λ b → hom (pr₂ (obs C c) b)))
                ) → (f ≡ coiter C)
            fin {C} (hom , _) = {!   !}

    Fin→Coh : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsFinCoalg M coiter → IsCohCoalg M coiter
    Fin→Coh {M} {coiter} isFinCoalg = λ C → λ f₁ → λ f₂ →
        let
            p =
                begin
                    f₁
                ≡⟨ isFinCoalg C f₁ ⟩
                    coiter C
                ≡⟨ isFinCoalg C f₂ ⁻¹ ⟩
                    f₂
                ∎
        in (≡-apply (ap fun p) , coh p) where
            coh : {C : Coalg} {f₁ f₂ : Mor C M} →
                ∏[ p ∈ f₁ ≡ f₂ ] ∏[ c ∈ ty C ]
                ap (obs M) (≡-apply (ap fun p) c) · com {C} {M} f₂ c ≡
                com {C} {M} f₁ c · ap (λ d → pr₁ (obs C c) , d) (inv (≡-apply , funext) (λ b → ≡-apply (ap fun p) (pr₂ (obs C c) b)))
            coh {C} {f} refl c =
                begin
                    refl · com {C} {M} f c
                ≡⟨ ·-neutr₁ (com {C} {M} f c) ⟩
                    com {C} {M} f c
                ≡⟨ ·-neutr₂ (com {C} {M} f c)⁻¹ ⟩
                    com {C} {M} f c · refl
                ≡⟨ ap (λ r → com {C} {M} f c · ap (λ d → pr₁ (obs C c) , d) r) (hom₁ (≡-apply , funext) refl)⁻¹ ⟩
                    com {C} {M} f c · ap (λ d → pr₁ (obs C c) , d) (inv (≡-apply , funext) (λ b → refl))
                ∎

    Coh→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsCohCoalg M coiter → IsTyBisimCoalg M coiter
    Coh→TyBisim {M} {coiter} isCohCoalg = λ ∼ → λ m₁ → λ m₂ → λ (s , p₁ , p₂) →
        p₁ ⁻¹ · pr₁ (isCohCoalg (coalg {M} ∼) (ρ₁ {M} ∼) (ρ₂ {M} ∼)) s · p₂

    TyBisim→FunBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisim→FunBisim {M} {coiter} isTyBisimCoalg = λ ∼ → λ m₁ → λ m₂ →
        isTyBisimCoalg (Fun→Ty {M} ∼) m₁ m₂ ∘ inv (Fun→Ty-pres {M} ∼ m₁ m₂)

    FunBisim→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] Mor C M} →
        IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    FunBisim→TyBisim {M} {coiter} isFunBisimCoalg = λ ∼ → λ m₁ → λ m₂ →
        isFunBisimCoalg (Ty→Fun {M} ∼) m₁ m₂
