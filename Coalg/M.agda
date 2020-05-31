{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    IsFinCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        Ty (ℓ-suc ℓ)
    IsFinCoalg M coiter = ∏[ C ∈ Coalg ] ∏[ f ∈ CoalgMor C M ] f ≡ coiter C

    FinCoalg : Ty (ℓ-suc ℓ)
    FinCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        IsFinCoalg M coiter


    IsCohCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        Ty (ℓ-suc ℓ)
    IsCohCoalg M coiter =
        ∏[ C ∈ Coalg ] ∏[ f₀ ∈ CoalgMor C M ] ∏[ f₁ ∈ CoalgMor C M ]
        ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ c ∈ ty C ]
        ap (λ f → obs M (f c)) p · ≡-apply (com f₁) c ≡
        ≡-apply (com f₀) c · ap (λ f → P-Fun f (obs C c)) p

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        IsCohCoalg M coiter


    IsTyBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        Ty (ℓ-suc ℓ)
    IsTyBisimCoalg M coiter =
        ∏[ ∼ ∈ TyBisim M ] TyBisimMor {M} ∼ (≡-TyBisim {M})

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        IsTyBisimCoalg M coiter


    IsFunBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        Ty (ℓ-suc ℓ)
    IsFunBisimCoalg M coiter =
        ∏[ ∼ ∈ FunBisim M ] FunBisimMor {M} ∼ (≡-FunBisim {M})

    FunBisimCoalg : Ty (ℓ-suc ℓ)
    FunBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ C ∈ Coalg ] CoalgMor C M) ]
        IsFunBisimCoalg M coiter


    CohCoalg→FinCoalg : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
        IsCohCoalg M coiter → IsFinCoalg M coiter
    CohCoalg→FinCoalg {M} {coiter} isCohCoalg = λ C → λ f →
        fin (isCohCoalg C f (coiter C))
        where
            fin : {C : Coalg} {f : CoalgMor C M} →
                (
                    ∑[ p ∈ fun f ≡ fun (coiter C) ] ∏[ c ∈ ty C ]
                    ap (λ f → obs M (f c)) p · ≡-apply (com (coiter C)) c ≡
                    ≡-apply (com f) c · ap (λ f → P-Fun f (obs C c)) p
                ) → (f ≡ coiter C)
            fin {C} {f} (refl , coh) =
                ≡-pair (
                    refl ,
                    (hom₀ (≡-apply , funext-axiom) (com f))⁻¹ ·
                    ap (funext) (funext (λ c →
                        (·-neutr₁ (≡-apply (com f) c))⁻¹ ·
                        (coh c)⁻¹ ·
                        (·-neutr₀ (≡-apply (com (coiter C)) c))
                    )) ·
                    (hom₀ (≡-apply , funext-axiom) (com (coiter C)))
                )

    FinCoalg→CohCoalg : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
        IsFinCoalg M coiter → IsCohCoalg M coiter
    FinCoalg→CohCoalg {M} {coiter} isFinCoalg = λ C → λ f₀ → λ f₁ →
        coh (isFinCoalg C f₀ · isFinCoalg C f₁ ⁻¹)
        where
            coh : {C : Coalg} {f₀ f₁ : CoalgMor C M} →
                (f₀ ≡ f₁) → (
                    ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ c ∈ ty C ]
                    ap (λ f → obs M (f c)) p · ≡-apply (com f₁) c ≡
                    ≡-apply (com f₀) c · ap (λ f → P-Fun f (obs C c)) p
                )
            coh {C} {f} {f} refl =
                (
                    refl ,
                    λ c →
                        ·-neutr₀ ( ≡-apply (com f) c) ·
                        ·-neutr₁ ( ≡-apply (com f) c)⁻¹
                )

    TyBisimCoalg→FunBisimCoalg : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisimCoalg→FunBisimCoalg {M} {coiter} isTyBisimCoalg = λ ∼ → {!   !}


    -- Fin→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
    --     IsFinCoalg M coiter → IsTyBisimCoalg M coiter
    -- Fin→TyBisim {M} {coiter} isFinCoalg = λ ∼ → λ m₀ → λ m₁ → λ (s , p₀ , p₁) →
    --     p₀ ⁻¹ ·
    --     ≡-apply (ap pr₀ (
    --         isFinCoalg (coalg ∼) (ρ₀ ∼) ·
    --         isFinCoalg (coalg ∼) (ρ₁ ∼)⁻¹
    --     )) s ·
    --     p₁


    -- Coh→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
    --     IsCohCoalg M coiter → IsTyBisimCoalg M coiter
    -- Coh→TyBisim {M} {coiter} isCohCoalg = λ ∼ → λ m₀ → λ m₁ → λ (s , p₀ , p₁) →
    --     p₀ ⁻¹ ·
    --     ≡-apply (pr₀ (isCohCoalg (coalg {M} ∼) (ρ₀ {M} ∼) (ρ₁ {M} ∼))) s ·
    --     p₁

    -- TyBisim→Coh : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
    --     IsTyBisimCoalg M coiter → IsCohCoalg M coiter
    -- TyBisim→Coh {M} {coiter} isTyBisimCoalg = λ C → λ f₀ → λ f₁ →
    --     (
    --         funext (λ c →
    --             isTyBisimCoalg
    --                 (C , f₀ , f₁)
    --                 (fun f₀ c)
    --                 (fun f₁ c)
    --                 (c , refl , refl)
    --         ) ,
    --         {!   !}
    --     )

    -- TyBisim→FunBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
    --     IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    -- TyBisim→FunBisim {M} {coiter} isTyBisimCoalg = λ ∼ → λ m₀ → λ m₁ →
    --     isTyBisimCoalg (Fun→Ty {M} ∼) m₀ m₁ ∘ inv (Fun→Ty-pres {M} ∼ m₀ m₁)
    --
    -- FunBisim→TyBisim : {M : Coalg} {coiter : ∏[ C ∈ Coalg ] CoalgMor C M} →
    --     IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    -- FunBisim→TyBisim {M} {coiter} isFunBisimCoalg = λ ∼ → λ m₀ → λ m₁ →
    --     isFunBisimCoalg (Ty→Fun {M} ∼) m₀ m₁
