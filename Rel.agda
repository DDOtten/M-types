{-# OPTIONS --without-K #-}


open import M-types.Ty
open import M-types.Sum
open import M-types.Prod
open import M-types.Eq
open import M-types.Equi


module M-types.Rel where
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

    ≡-TyRel : {X : Ty ℓ} →
        TyRel X
    ≡-TyRel {_} {X} = (X , id , id)


    TyRelMor : {X : Ty ℓ} →
        TyRel X → TyRel X → Ty ℓ
    TyRelMor {_} {X} ∼ ≈ =
        ∑[ fun ∈ (ty ∼ → ty ≈) ]
        (ρ₀ ≈ ∘ fun ≡ ρ₀ ∼) × (ρ₁ ≈ ∘ fun ≡ ρ₁ ∼)


    FunRel : Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    FunRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ] Ty ℓ
    FunRel-syntax ∼ x₀ x₁ = ∼ x₀ x₁
    syntax FunRel-syntax ∼ x₀ x₁ = x₀ [ ∼ ] x₁

    ≡-FunRel : {X : Ty ℓ} →
        FunRel X
    ≡-FunRel = λ x₀ → λ x₁ → x₀ ≡ x₁


    FunRelMor : {X : Ty ℓ} →
        FunRel X → FunRel X → Ty ℓ
    FunRelMor {_} {X} ∼ ≈ =
        ∏[ x₀ ∈ X ] ∏[ x₁ ∈ X ]
        (x₀ [ ∼ ] x₁ → x₀ [ ≈ ] x₁)


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
    FunRel→TyRel-pres {_} {X} ∼ x₀ x₁ =
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


    TyRelMor→FunRelMor : {X : Ty ℓ} {∼ ≈ : TyRel X} →
        TyRelMor ∼ ≈ → FunRelMor (TyRel→FunRel ∼) (TyRel→FunRel ≈)
    TyRelMor→FunRelMor {_} {X} {∼} {≈} (fun , refl , refl) x₀ x₁ (s , refl , refl) =
        (
            fun s ,
            refl ,
            refl
        )

    FunRelMor→TyRelMor : {X : Ty ℓ} {∼ ≈ : FunRel X} →
        FunRelMor ∼ ≈ → TyRelMor (FunRel→TyRel ∼) (FunRel→TyRel ≈)
    FunRelMor→TyRelMor {_} {X} {∼} {≈} mor =
        (
            (λ (x₀ , x₁ , s) → (x₀ , x₁ , mor x₀ x₁ s)) ,
            refl ,
            refl
        )
