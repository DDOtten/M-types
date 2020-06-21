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
        ∏[ ∼ ∈ TyBisim M ] TyRelMor (tyRel {M} ∼) ≡-tyRel

    TyBisimCoalg : Ty (ℓ-suc ℓ)
    TyBisimCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsTyBisimCoalg M coiter


    IsFunBisimCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsFunBisimCoalg M coiter =
        ∏[ ∼ ∈ FunBisim M ] FunRelMor (funRel {M} ∼) ≡-funRel

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

    CohCoalg→TyBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohCoalg M coiter → IsTyBisimCoalg M coiter
    CohCoalg→TyBisimCoalg {M} {coiter} isCohCoalg = λ ∼ →
        (
            fun (ρ₀ ∼) ,
            refl ,
            pr₀ (isCohCoalg (ty ∼) (ρ₀ ∼) (ρ₁ ∼))
        )

    -- TyBisimCoalg→FunBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
    --     IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    -- TyBisimCoalg→FunBisimCoalg {M} {coiter} isTyBisimCoalg = λ ∼ →
    --     {! TyRelMor→FunRelMor (isTyBisimCoalg (FunBisim→TyBisim ∼))  !}

    TyBisimCoalg→FunBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisimCoalg→FunBisimCoalg {M} {coiter} isTyBisimCoalg = λ ∼ → (
        let
            f : FunRelMor (funRel {M} ∼) (TyRel→FunRel (FunRel→TyRel (funRel {M} ∼)))
            f = FunRel→FunRel-mor (funRel {M} ∼)
            g : FunRelMor (TyRel→FunRel (FunRel→TyRel (funRel {M} ∼))) (TyRel→FunRel ≡-tyRel)
            g = TyRelMor→FunRelMor (isTyBisimCoalg (FunBisim→TyBisim {M} ∼))
            h : FunRelMor (TyRel→FunRel ≡-tyRel) ≡-funRel
            h = FunRel-≡-mor
        in
            h ∘-funRel (g ∘-funRel f)
        )

    FunBisimCoalg→TyBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    FunBisimCoalg→TyBisimCoalg {M} {coiter} isFunBisimCoalg = λ ∼ → (
        let
            f : TyRelMor (tyRel {M} ∼) (FunRel→TyRel (TyRel→FunRel (tyRel {M} ∼)))
            f = TyRel→TyRel-mor (tyRel {M} ∼)
            g : TyRelMor (FunRel→TyRel (TyRel→FunRel (tyRel {M} ∼))) (FunRel→TyRel ≡-funRel)
            g = FunRelMor→TyRelMor (isFunBisimCoalg (TyBisim→FunBisim {M} ∼))
            h : TyRelMor (FunRel→TyRel ≡-funRel) ≡-tyRel
            h = TyRel-≡-mor
        in
            -- h ∘-tyRel (g ∘-tyRel f)
            _∘-tyRel_ {ℓ} {ty M} {tyRel {M} ∼} {FunRel→TyRel ≡-funRel} {≡-tyRel}
            h
            (_∘-tyRel_ {ℓ} {ty M} {tyRel {M} ∼} {FunRel→TyRel (TyRel→FunRel (tyRel {M} ∼))} {FunRel→TyRel ≡-funRel} g f)
        )
