{-# OPTIONS --without-K #-}


open import M-types.Base.Core
open import M-types.Base.Sum
open import M-types.Base.Prod
open import M-types.Base.Eq
open import M-types.Base.Equi
open import M-types.Base.Axiom


module M-types.Base.Rel where
    TyRel : Ty ℓ → Ty (ℓ-suc ℓ)
    TyRel {ℓ} X = ∑[ ty ∈ Ty ℓ ] (ty → X) × (ty → X)

    ρ₀ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Y (pr₀ s)
    ρ₀ = pr₀ ∘ pr₁

    ρ₁ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Z (pr₀ s)
    ρ₁ = pr₁ ∘ pr₁

    TyRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ] Ty ℓ
    TyRel-syntax ∼ x₀ x₁ = ∑[ s ∈ (ty ∼) ] ((ρ₀ ∼ s ≡ x₀) × (ρ₁ ∼ s ≡ x₁))
    syntax TyRel-syntax ∼ x₀ x₁ = x₀ ⟨ ∼ ⟩ x₁

    ≡-tyRel : {X : Ty ℓ} →
        TyRel X
    ≡-tyRel {_} {X} = (X , id , id)


    TyRelMor : {X : Ty ℓ} →
        TyRel X → TyRel X → Ty ℓ
    TyRelMor {_} {X} ∼ ≈ =
        ∑[ fun ∈ (ty ∼ → ty ≈) ]
        (ρ₀ ≈ ∘ fun ≡ ρ₀ ∼) × (ρ₁ ≈ ∘ fun ≡ ρ₁ ∼)

    com₀ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Y (pr₀ s)
    com₀ = pr₀ ∘ pr₁

    com₁ : {X : Ty ℓ₀} {Y Z : X → Ty ℓ₁} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Z (pr₀ s)
    com₁ = pr₁ ∘ pr₁

    id-tyRel : {X : Ty ℓ} {∼ : TyRel X} →
        TyRelMor ∼ ∼
    id-tyRel {_} {X} {∼} = (id , refl , refl)

    infixr 9 _∘-tyRel_
    _∘-tyRel_ : {X : Ty ℓ} {∼₀ ∼₁ ∼₂ : TyRel X} →
        TyRelMor ∼₁ ∼₂ → TyRelMor ∼₀ ∼₁ → TyRelMor ∼₀ ∼₂
    g ∘-tyRel f =
        (
            fun g ∘ fun f ,
            ap (λ k → k ∘ fun f) (com₀ g) · com₀ f ,
            ap (λ k → k ∘ fun f) (com₁ g) · com₁ f
        )


    FunRel : Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    FunRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ] Ty ℓ
    FunRel-syntax ∼ x₀ x₁ = ∼ x₀ x₁
    syntax FunRel-syntax ∼ x₀ x₁ = x₀ [ ∼ ] x₁

    ≡-funRel : {X : Ty ℓ} →
        FunRel X
    ≡-funRel = λ x₀ → λ x₁ → x₀ ≡ x₁


    FunRelMor : {X : Ty ℓ} →
        FunRel X → FunRel X → Ty ℓ
    FunRelMor {_} {X} ∼ ≈ =
        ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ [ ∼ ] x₁ → x₀ [ ≈ ] x₁)

    id-funRel : {X : Ty ℓ} {∼ : FunRel X} →
        FunRelMor ∼ ∼
    id-funRel {_} {X} {∼} = λ x₀ → λ x₁ → id

    infixr 9 _∘-funRel_
    _∘-funRel_ : {X : Ty ℓ} {∼₀ ∼₁ ∼₂ : FunRel X} →
        FunRelMor ∼₁ ∼₂ → FunRelMor ∼₀ ∼₁ → FunRelMor ∼₀ ∼₂
    g ∘-funRel f = λ x₀ → λ x₁ → g x₀ x₁ ∘ f x₀ x₁


    TyRel→FunRel : {X : Ty ℓ} →
        TyRel X → FunRel X
    TyRel→FunRel {_} {X} ∼ = λ x₀ → λ x₁ → x₀ ⟨ ∼ ⟩ x₁

    FunRel→TyRel : {X : Ty ℓ} →
        FunRel X → TyRel X
    FunRel→TyRel {_} {X} ∼ =
        (
            (∑[ x₀ ∈ X ] ∑[ x₁ ∈ X ] x₀ [ ∼ ] x₁) ,
            pr₀ ,
            pr₀ ∘ pr₁
        )


    TyRel→FunRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ [ TyRel→FunRel ∼ ] x₁) ≡ (x₀ ⟨ ∼ ⟩ x₁)
    TyRel→FunRel-pres ∼ x₀ x₁ = refl

    FunRel→TyRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ ⟨ FunRel→TyRel ∼ ⟩ x₁) ≃ (x₀ [ ∼ ] x₁)
    FunRel→TyRel-pres ∼ x₀ x₁ =
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


    TyRel→TyRel-mor : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] TyRelMor ∼ (FunRel→TyRel (TyRel→FunRel ∼))
    TyRel→TyRel-mor ∼ =
        (
            (λ s → (ρ₀ ∼ s , ρ₁ ∼ s , (s , refl , refl))) ,
            refl ,
            refl
        )

    FunRel→FunRel-mor : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] FunRelMor ∼ (TyRel→FunRel (FunRel→TyRel ∼))
    FunRel→FunRel-mor ∼ = λ x₀ → λ x₁ → λ s → ((x₀ , x₁ , s) , refl , refl)


    ≡-TyRel→FunRel-mor : {X : Ty ℓ} →
        FunRelMor {ℓ} {X} (TyRel→FunRel ≡-tyRel) ≡-funRel
    ≡-TyRel→FunRel-mor = λ x₀ → λ x₁ → λ(s , p₀ , p₁) → p₀ ⁻¹ · p₁

    ≡-FunRel→TyRel-mor : {X : Ty ℓ} →
        TyRelMor {ℓ} {X} (FunRel→TyRel ≡-funRel) ≡-tyRel
    ≡-FunRel→TyRel-mor =
        (
            (λ (x₀ , x₁ , p) → x₀) ,
            refl ,
            funext (λ (x₀ , x₁ , p) → p)
        )


    TyRelMor→FunRelMor : {X : Ty ℓ} {∼ ≈ : TyRel X} →
        TyRelMor ∼ ≈ → FunRelMor (TyRel→FunRel ∼) (TyRel→FunRel ≈)
    TyRelMor→FunRelMor (fun , refl , refl) x₀ x₁ (s , refl , refl) =
        (
            fun s ,
            refl ,
            refl
        )

    FunRelMor→TyRelMor : {X : Ty ℓ} {∼ ≈ : FunRel X} →
        FunRelMor ∼ ≈ → TyRelMor (FunRel→TyRel ∼) (FunRel→TyRel ≈)
    FunRelMor→TyRelMor f =
        (
            (λ (x₀ , x₁ , s) → (x₀ , x₁ , f x₀ x₁ s)) ,
            refl {_} {_} {pr₀}  ,
            refl
        )
