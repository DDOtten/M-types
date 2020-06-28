{-# OPTIONS --without-K #-}


open import M-types.Base.Core
open import M-types.Base.Sum
open import M-types.Base.Prod
open import M-types.Base.Eq
open import M-types.Base.Equi
open import M-types.Base.Axiom


module M-types.Base.Rel where
    SpanRel : Ty ℓ → Ty (ℓ-suc ℓ)
    SpanRel {ℓ} X = ∑[ ty ∈ Ty ℓ ] (ty → X) × (ty → X)

    ρ₀ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Y (pr₀ s)
    ρ₀ = pr₀ ∘ pr₁

    ρ₁ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Z (pr₀ s)
    ρ₁ = pr₁ ∘ pr₁

    SpanRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ SpanRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ] Ty ℓ
    SpanRel-syntax ∼ x₀ x₁ = ∑[ s ∈ (ty ∼) ] ((ρ₀ ∼ s ≡ x₀) × (ρ₁ ∼ s ≡ x₁))
    syntax SpanRel-syntax ∼ x₀ x₁ = x₀ ⟨ ∼ ⟩ x₁

    ≡-spanRel : {X : Ty ℓ} →
        SpanRel X
    ≡-spanRel {_} {X} = (X , id , id)


    SpanRelMor : {X : Ty ℓ} →
        SpanRel X → SpanRel X → Ty ℓ
    SpanRelMor {_} {X} ∼ ≈ =
        ∑[ fun ∈ (ty ∼ → ty ≈) ]
        (ρ₀ ≈ ∘ fun ≡ ρ₀ ∼) × (ρ₁ ≈ ∘ fun ≡ ρ₁ ∼)

    com₀ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Y (pr₀ s)
    com₀ = pr₀ ∘ pr₁

    com₁ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Z (pr₀ s)
    com₁ = pr₁ ∘ pr₁

    id-spanRel : {X : Ty ℓ} {∼ : SpanRel X} →
        SpanRelMor ∼ ∼
    id-spanRel {_} {X} {∼} = (id , refl , refl)

    infixr 9 _∘-spanRel_
    _∘-spanRel_ : {X : Ty ℓ} {∼₀ ∼₁ ∼₂ : SpanRel X} →
        SpanRelMor ∼₁ ∼₂ → SpanRelMor ∼₀ ∼₁ → SpanRelMor ∼₀ ∼₂
    g ∘-spanRel f =
        (
            fun g ∘ fun f ,
            ap (λ k → k ∘ fun f) (com₀ g) · com₀ f ,
            ap (λ k → k ∘ fun f) (com₁ g) · com₁ f
        )


    DepRel : Ty ℓ → Ty (ℓ-suc ℓ)
    DepRel {ℓ} X = X → X → Ty ℓ

    DepRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ DepRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ] Ty ℓ
    DepRel-syntax ∼ x₀ x₁ = ∼ x₀ x₁
    syntax DepRel-syntax ∼ x₀ x₁ = x₀ [ ∼ ] x₁

    ≡-depRel : {X : Ty ℓ} →
        DepRel X
    ≡-depRel = λ x₀ → λ x₁ → x₀ ≡ x₁


    DepRelMor : {X : Ty ℓ} →
        DepRel X → DepRel X → Ty ℓ
    DepRelMor {_} {X} ∼ ≈ =
        ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ [ ∼ ] x₁ → x₀ [ ≈ ] x₁)

    id-depRel : {X : Ty ℓ} {∼ : DepRel X} →
        DepRelMor ∼ ∼
    id-depRel {_} {X} {∼} = λ x₀ → λ x₁ → id

    infixr 9 _∘-depRel_
    _∘-depRel_ : {X : Ty ℓ} {∼₀ ∼₁ ∼₂ : DepRel X} →
        DepRelMor ∼₁ ∼₂ → DepRelMor ∼₀ ∼₁ → DepRelMor ∼₀ ∼₂
    g ∘-depRel f = λ x₀ → λ x₁ → g x₀ x₁ ∘ f x₀ x₁


    SpanRel→DepRel : {X : Ty ℓ} →
        SpanRel X → DepRel X
    SpanRel→DepRel {_} {X} ∼ = λ x₀ → λ x₁ → x₀ ⟨ ∼ ⟩ x₁

    DepRel→SpanRel : {X : Ty ℓ} →
        DepRel X → SpanRel X
    DepRel→SpanRel {_} {X} ∼ =
        (
            (∑[ x₀ ∈ X ] ∑[ x₁ ∈ X ] x₀ [ ∼ ] x₁) ,
            pr₀ ,
            pr₀ ∘ pr₁
        )


    SpanRel→DepRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ SpanRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ [ SpanRel→DepRel ∼ ] x₁) ≡ (x₀ ⟨ ∼ ⟩ x₁)
    SpanRel→DepRel-pres ∼ x₀ x₁ = refl

    DepRel→SpanRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ DepRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ ⟨ DepRel→SpanRel ∼ ⟩ x₁) ≃ (x₀ [ ∼ ] x₁)
    DepRel→SpanRel-pres ∼ x₀ x₁ =
        (
            (λ ((y₀ , y₁ , s) , p₀ , p₁) →
                tra (λ x → x [ ∼ ] x₁) p₀ (tra (λ y → y₀ [ ∼ ] y) p₁ s)
            ) ,
            Qinv→IsEqui (
                (λ s → ((x₀ , x₁ , s) , refl , refl)) ,
                (λ {((x₀ , x₁ , s) , refl , refl) → refl}) ,
                (λ s → refl)
            )
        )


    SpanRel→SpanRel-mor : {X : Ty ℓ} →
        ∏[ ∼ ∈ SpanRel X ] SpanRelMor ∼ (DepRel→SpanRel (SpanRel→DepRel ∼))
    SpanRel→SpanRel-mor ∼ =
        (
            (λ s → (ρ₀ ∼ s , ρ₁ ∼ s , (s , refl , refl))) ,
            refl ,
            refl
        )

    DepRel→DepRel-mor : {X : Ty ℓ} →
        ∏[ ∼ ∈ DepRel X ] DepRelMor ∼ (SpanRel→DepRel (DepRel→SpanRel ∼))
    DepRel→DepRel-mor ∼ = λ x₀ → λ x₁ → λ s → ((x₀ , x₁ , s) , refl , refl)


    ≡-SpanRel→DepRel-mor : {X : Ty ℓ} →
        DepRelMor {ℓ} {X} (SpanRel→DepRel ≡-spanRel) ≡-depRel
    ≡-SpanRel→DepRel-mor = λ x₀ → λ x₁ → λ(s , p₀ , p₁) → p₀ ⁻¹ · p₁

    ≡-DepRel→SpanRel-mor : {X : Ty ℓ} →
        SpanRelMor {ℓ} {X} (DepRel→SpanRel ≡-depRel) ≡-spanRel
    ≡-DepRel→SpanRel-mor =
        (
            (λ (x₀ , x₁ , p) → x₀) ,
            refl ,
            funext (λ (x₀ , x₁ , p) → p)
        )


    SpanRelMor→DepRelMor : {X : Ty ℓ} {∼ ≈ : SpanRel X} →
        SpanRelMor ∼ ≈ → DepRelMor (SpanRel→DepRel ∼) (SpanRel→DepRel ≈)
    SpanRelMor→DepRelMor (fun , refl , refl) x₀ x₁ (s , refl , refl) =
        (
            fun s ,
            refl ,
            refl
        )

    DepRelMor→SpanRelMor : {X : Ty ℓ} {∼ ≈ : DepRel X} →
        DepRelMor ∼ ≈ → SpanRelMor (DepRel→SpanRel ∼) (DepRel→SpanRel ≈)
    DepRelMor→SpanRelMor f =
        (
            (λ (x₀ , x₁ , s) → (x₀ , x₁ , f x₀ x₁ s)) ,
            refl {_} {_} {pr₀}  ,
            refl
        )
