{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.M {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B
    open import M-types.Coalg.Bisim A B


    IsFinM : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsFinM M coiter = ∏[ X ∈ Coalg ] ∏[ f ∈ CoalgMor X M ] f ≡ coiter X

    FinM : Ty (ℓ-suc ℓ)
    FinM = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsFinM M coiter


    IsCohM : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsCohM M coiter =
        ∏[ X ∈ Coalg ] ∏[ f₀ ∈ CoalgMor X M ] ∏[ f₁ ∈ CoalgMor X M ]
        ∑[ p ∈ fun f₀ ≡ fun f₁ ] ∏[ x ∈ ty X ]
        ap (λ f → obs M (f x)) p · ≡-apply (com f₁) x ≡
        ≡-apply (com f₀) x · ap (λ f → P-Fun f (obs X x)) p

    CohM : Ty (ℓ-suc ℓ)
    CohM = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsCohM M coiter


    IsBareM : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsBareM M coiter =
        ∏[ X ∈ Coalg ] ∏[ f₀ ∈ CoalgMor X M ] ∏[ f₁ ∈ CoalgMor X M ]
        (fun f₀ ≡ fun f₁)

    BareM : Ty (ℓ-suc ℓ)
    BareM = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsBareM M coiter


    IsTyBisimM : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsTyBisimM M coiter =
        ∏[ ∼ ∈ TyBisim M ] SpanRelMor (spanRel {M} ∼) ≡-spanRel

    TyBisimM : Ty (ℓ-suc ℓ)
    TyBisimM = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsTyBisimM M coiter


    IsFunBisimM : ∏[ M ∈ Coalg ] ∏[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        Ty (ℓ-suc ℓ)
    IsFunBisimM M coiter =
        ∏[ ∼ ∈ FunBisim M ] DepRelMor (depRel {M} ∼) ≡-depRel

    FunBisimM : Ty (ℓ-suc ℓ)
    FunBisimM = ∑[ M ∈ Coalg ] ∑[ coiter ∈ (∏[ X ∈ Coalg ] CoalgMor X M) ]
        IsFunBisimM M coiter


    FinM→CohM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFinM M coiter → IsCohM M coiter
    FinM→CohM {M} {coiter} isFin = λ X → λ f₀ → λ f₁ →
        coh (isFin X f₀ · isFin X f₁ ⁻¹)
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

    CohM→FinM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohM M coiter → IsFinM M coiter
    CohM→FinM {M} {coiter} isCoh = λ X → λ f →
        fin (isCoh X f (coiter X))
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

    CohM→BareM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsCohM M coiter → IsBareM M coiter
    CohM→BareM {M} {coiter} isCoh = λ X → λ f₀ → λ f₁ → pr₀ (isCoh X f₀ f₁)

    BareM→TyBisimM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsBareM M coiter → IsTyBisimM M coiter
    BareM→TyBisimM {M} {coiter} isBare = λ ∼ →
        (
            fun (ρ₀ ∼) ,
            refl ,
            isBare (ty ∼) (ρ₀ ∼) (ρ₁ ∼)
        )

    TyBisimM→BareM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimM M coiter → IsBareM M coiter
    TyBisimM→BareM {M} {coiter} isTyBisim = λ X → λ f₀ → λ f₁ →
        funext (λ x →
            (≡-apply (com₀ (isTyBisim (X , f₀ , f₁))) x) ⁻¹ ·
            (≡-apply (com₁ (isTyBisim (X , f₀ , f₁))) x)
        )

    TyBisimM→FunBisimM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsTyBisimM M coiter → IsFunBisimM M coiter
    TyBisimM→FunBisimM {M} {coiter} isTyBisim = λ ∼ → let
            f : DepRelMor (depRel {M} ∼) (SpanRel→DepRel (DepRel→SpanRel (depRel {M} ∼)))
            f = DepRel→DepRel-mor (depRel {M} ∼)
            g : DepRelMor (SpanRel→DepRel (DepRel→SpanRel (depRel {M} ∼))) (SpanRel→DepRel ≡-spanRel)
            g = SpanRelMor→DepRelMor (isTyBisim (FunBisim→TyBisim {M} ∼))
            h : DepRelMor (SpanRel→DepRel ≡-spanRel) ≡-depRel
            h = ≡-SpanRel→DepRel-mor
        in
            h ∘-depRel (g ∘-depRel f)

    FunBisimM→TyBisimM : {M : Coalg} {coiter : ∏[ X ∈ Coalg ] CoalgMor X M} →
        IsFunBisimM M coiter → IsTyBisimM M coiter
    FunBisimM→TyBisimM {M} {coiter} isFunBisim = λ ∼ → let
            f : SpanRelMor (spanRel {M} ∼) (DepRel→SpanRel (SpanRel→DepRel (spanRel {M} ∼)))
            f = SpanRel→SpanRel-mor (spanRel {M} ∼)
            g : SpanRelMor (DepRel→SpanRel (SpanRel→DepRel (spanRel {M} ∼))) (DepRel→SpanRel ≡-depRel)
            g = DepRelMor→SpanRelMor (isFunBisim (TyBisim→FunBisim {M} ∼))
            h : SpanRelMor (DepRel→SpanRel ≡-depRel) ≡-spanRel
            h = ≡-DepRel→SpanRel-mor
        in
            -- h ∘-spanRel (g ∘-spanRel f)
            _∘-spanRel_ {ℓ} {ty M} {spanRel {M} ∼} {DepRel→SpanRel ≡-depRel} {≡-spanRel}
            h
            (_∘-spanRel_ {ℓ} {ty M} {spanRel {M} ∼} {DepRel→SpanRel (SpanRel→DepRel (spanRel {M} ∼))} {DepRel→SpanRel ≡-depRel} g f)
