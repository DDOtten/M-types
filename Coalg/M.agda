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
        ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ x ∈ ty X ]
        ap (λ f → obs M (f x)) p · ≡-apply (com f₁) x ≡
        ≡-apply (com f₀) x · ap (λ f → P-Fun f (obs X x)) p

    CohCoalg : Ty (ℓ-suc ℓ)
    CohCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsCohCoalg M coiter


    IsBareCoalg : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsBareCoalg M coiter =
        ∏[ X ∈ Coalg ] ∏[ f₀ ∈ CoalgMor X M ] ∏[ f₁ ∈ CoalgMor X M ]
        (fun f₀ ≡ fun f₁)

    BareCoalg : Ty (ℓ-suc ℓ)
    BareCoalg = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsBareCoalg M coiter


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


    FinCoalg→CohCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFinCoalg M coiter → IsCohCoalg M coiter
    FinCoalg→CohCoalg {M} {coiter} isFinCoalg = λ X → λ f₀ → λ f₁ →
        coh (isFinCoalg X f₀ · isFinCoalg X f₁ ⁻¹)
        where
            coh : {X : Coalg} {f₀ f₁ : CoalgMor X M} →
                (f₀ ≡ f₁) → (
                    ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ x ∈ ty X ]
                    ap (λ f → obs M (f x)) p · ≡-apply (com f₁) x ≡
                    ≡-apply (com f₀) x · ap (λ f → P-Fun f (obs X x)) p
                )
            coh {X} {f} {f} refl =
                (
                    refl ,
                    λ x →
                        ·-neutr₀ ( ≡-apply (com f) x) ·
                        ·-neutr₁ ( ≡-apply (com f) x) ⁻¹
                )

    CohCoalg→FinCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohCoalg M coiter → IsFinCoalg M coiter
    CohCoalg→FinCoalg {M} {coiter} isCohCoalg = λ X → λ f →
        fin (isCohCoalg X f (coiter X))
        where
            fin : {X : Coalg} {f : CoalgMor X M} →
                (
                    ∑[ p ∈ fun f ≡ fun (coiter X) ] ∏[ x ∈ ty X ]
                    ap (λ f → obs M (f x)) p · ≡-apply (com (coiter X)) x ≡
                    ≡-apply (com f) x · ap (λ f → P-Fun f (obs X x)) p
                ) → (f ≡ coiter X)
            fin {X} {f} (refl , coh) =
                ≡-pair (
                    refl ,
                    (hom₀ (≡-apply , funext-axiom) (com f)) ⁻¹ ·
                    ap funext (funext (λ x →
                        (·-neutr₁ (≡-apply (com f) x)) ⁻¹ ·
                        (coh x) ⁻¹ ·
                        (·-neutr₀ (≡-apply (com (coiter X)) x))
                    )) ·
                    (hom₀ (≡-apply , funext-axiom) (com (coiter X)))
                )

    CohCoalg→BareCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohCoalg M coiter → IsBareCoalg M coiter
    CohCoalg→BareCoalg {M} {coiter} isCohCoalg = λ X → λ f₀ → λ f₁ → pr₀ (isCohCoalg X f₀ f₁)

    BareCoalg→TyBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsBareCoalg M coiter → IsTyBisimCoalg M coiter
    BareCoalg→TyBisimCoalg {M} {coiter} isBareCoalg = λ ∼ →
        (
            fun (ρ₀ ∼) ,
            refl ,
            isBareCoalg (ty ∼) (ρ₀ ∼) (ρ₁ ∼)
        )

    TyBisimCoalg→BareCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimCoalg M coiter → IsBareCoalg M coiter
    TyBisimCoalg→BareCoalg {M} {coiter} isTyBisimCoalg = λ X → λ f₀ → λ f₁ →
        funext (λ x →
            (≡-apply (com₀ (isTyBisimCoalg (X , f₀ , f₁))) x) ⁻¹ ·
            (≡-apply (com₁ (isTyBisimCoalg (X , f₀ , f₁))) x)
        )

    TyBisimCoalg→FunBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimCoalg M coiter → IsFunBisimCoalg M coiter
    TyBisimCoalg→FunBisimCoalg {M} {coiter} isTyBisimCoalg = λ ∼ → let
            f : FunRelMor (funRel {M} ∼) (TyRel→FunRel (FunRel→TyRel (funRel {M} ∼)))
            f = FunRel→FunRel-mor (funRel {M} ∼)
            g : FunRelMor (TyRel→FunRel (FunRel→TyRel (funRel {M} ∼))) (TyRel→FunRel ≡-tyRel)
            g = TyRelMor→FunRelMor (isTyBisimCoalg (FunBisim→TyBisim {M} ∼))
            h : FunRelMor (TyRel→FunRel ≡-tyRel) ≡-funRel
            h = FunRel-≡-mor
        in
            h ∘-funRel (g ∘-funRel f)

    FunBisimCoalg→TyBisimCoalg : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFunBisimCoalg M coiter → IsTyBisimCoalg M coiter
    FunBisimCoalg→TyBisimCoalg {M} {coiter} isFunBisimCoalg = λ ∼ → let
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
