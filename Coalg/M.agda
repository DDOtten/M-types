{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    IsFinCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsFinCoalg M coiter = ∏[ X ∈ Coalg ] ∏[ f ∈ CoalgMor X M ] f ≡ coiter X

    FinCoalg : Ty (ℓ-suc ℓ)
    FinCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsFinCoalg M coiter


    IsCohCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsCohCoalg M coiter =
        ∏[ X ∈ Coalg ] ∏[ f₀ ∈ CoalgMor X M ] ∏[ f₁ ∈ CoalgMor X M ]
        ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ d ∈ ty X ]
        ap (λ f → obs M (f d)) p · ≡-apply (com f₁) d ≡
        ≡-apply (com f₀) d · ap (λ f → P-Fun f (obs X d)) p

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsCohCoalg M coiter


    IsTyBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsTyBisimCoalg M coiter =
        ∏[ ∼ ∈ TyBisim M ] TyBisimMor {M} ∼ (≡-TyBisim {M})

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsTyBisimCoalg M coiter


    IsFunBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsFunBisimCoalg M coiter =
        ∏[ ∼ ∈ FunBisim M ] FunBisimMor {M} ∼ (≡-FunBisim {M})

    FunBisimCoalg : Ty (ℓ-suc ℓ)
    FunBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsFunBisimCoalg M coiter


    CohCoalg→FinCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohCoalg M coiter → IsFinCoalg M coiter
    CohCoalg→FinCoalg {M} {coiter} isCohCoalg = λ X → λ f →
        fin (isCohCoalg X f (coiter X))
        where
            fin : {X : Coalg} {f : CoalgMor X M} →
                (
                    ∑[ p ∈ fun f ≡ fun (coiter X) ] ∏[ d ∈ ty X ]
                    ap (λ f → obs M (f d)) p · ≡-apply (com (coiter X)) d ≡
                    ≡-apply (com f) d · ap (λ f → P-Fun f (obs X d)) p
                ) → (f ≡ coiter X)
            fin {X} {f} (refl , coh) =
                ≡-pair (
                    refl ,
                    (hom₀ (≡-apply , funext-axiom) (com f))⁻¹ ·
                    ap (funext) (funext (λ d →
                        (·-neutr₁ (≡-apply (com f) d))⁻¹ ·
                        (coh d)⁻¹ ·
                        (·-neutr₀ (≡-apply (com (coiter X)) d))
                    )) ·
                    (hom₀ (≡-apply , funext-axiom) (com (coiter X)))
                )

    FinCoalg→CohCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFinCoalg M coiter → IsCohCoalg M coiter
    FinCoalg→CohCoalg {M} {coiter} isFinCoalg = λ X → λ f₀ → λ f₁ →
        coh (isFinCoalg X f₀ · isFinCoalg X f₁ ⁻¹)
        where
            coh : {X : Coalg} {f₀ f₁ : CoalgMor X M} →
                (f₀ ≡ f₁) → (
                    ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ d ∈ ty X ]
                    ap (λ f → obs M (f d)) p · ≡-apply (com f₁) d ≡
                    ≡-apply (com f₀) d · ap (λ f → P-Fun f (obs X d)) p
                )
            coh {X} {f} {f} refl =
                (
                    refl ,
                    λ d →
                        ·-neutr₀ ( ≡-apply (com f) d) ·
                        ·-neutr₁ ( ≡-apply (com f) d)⁻¹
                )

    TyBisimCoalg→FunBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisimCoalg→FunBisimCoalg {M} {coiter} isTyBisimCoalg = λ ∼ → {!   !}


    -- Fin→TyBisim : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsFinCoalg M coiter → IsTyBisimCoalg M coiter
    -- Fin→TyBisim {M} {coiter} isFinCoalg = λ ∼ → λ m₀ → λ m₁ → λ (s , p₀ , p₁) →
    --     p₀ ⁻¹ ·
    --     ≡-apply (ap pr₀ (
    --         isFinCoalg (coalg ∼) (ρ₀ ∼) ·
    --         isFinCoalg (coalg ∼) (ρ₁ ∼)⁻¹
    --     )) s ·
    --     p₁


    -- Coh→TyBisim : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsCohCoalg M coiter → IsTyBisimCoalg M coiter
    -- Coh→TyBisim {M} {coiter} isCohCoalg = λ ∼ → λ m₀ → λ m₁ → λ (s , p₀ , p₁) →
    --     p₀ ⁻¹ ·
    --     ≡-apply (pr₀ (isCohCoalg (coalg {M} ∼) (ρ₀ {M} ∼) (ρ₁ {M} ∼))) s ·
    --     p₁

    -- TyBisim→Coh : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsTyBisimCoalg M coiter → IsCohCoalg M coiter
    -- TyBisim→Coh {M} {coiter} isTyBisimCoalg = λ X → λ f₀ → λ f₁ →
    --     (
    --         funext (λ d →
    --             isTyBisimCoalg
    --                 (X , f₀ , f₁)
    --                 (fun f₀ d)
    --                 (fun f₁ d)
    --                 (d , refl , refl)
    --         ) ,
    --         {!   !}
    --     )

    -- TyBisim→FunBisim : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    -- TyBisim→FunBisim {M} {coiter} isTyBisimCoalg = λ ∼ → λ m₀ → λ m₁ →
    --     isTyBisimCoalg (Fun→Ty {M} ∼) m₀ m₁ ∘ inv (Fun→Ty-pres {M} ∼ m₀ m₁)
    --
    -- FunBisim→TyBisim : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    -- FunBisim→TyBisim {M} {coiter} isFunBisimCoalg = λ ∼ → λ m₀ → λ m₁ →
    --     isFunBisimCoalg (Ty→Fun {M} ∼) m₀ m₁
