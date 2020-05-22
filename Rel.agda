{-# OPTIONS --without-K #-}


open import M-types.Ty
open import M-types.Sum
open import M-types.Prod
open import M-types.Eq
open import M-types.Equi


module M-types.Rel where
    TyRel : Ty ℓ → Ty (ℓ-suc ℓ)
    TyRel {ℓ} X = ∑[ ty ∈ Ty ℓ ] (ty → X) × (ty → X)

    ρ₁ : {X : Ty ℓ₁} {Y Z : X → Ty ℓ₂} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Y (pr₁ s)
    ρ₁ = pr₁ ∘ pr₂

    ρ₂ : {X : Ty ℓ₁} {Y Z : X → Ty ℓ₂} →
        ∏[ s ∈ ∑[ x ∈ X ] (Y x × Z x) ] Z (pr₁ s)
    ρ₂ = pr₂ ∘ pr₂

    TyRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    TyRel-syntax ∼ x₁ x₂ = ∑[ s ∈ (ty ∼) ] ((ρ₁ ∼ s ≡ x₁) × (ρ₂ ∼ s ≡ x₂))
    syntax TyRel-syntax ∼ x₁ x₂ = x₁ ⟨ ∼ ⟩ x₂

    ≡-TyRel : {X : Ty ℓ} →
        TyRel X
    ≡-TyRel {_} {X} = (X , id , id)


    TyRelMor : {X : Ty ℓ} →
        TyRel X → TyRel X → Ty ℓ
    TyRelMor {_} {X} ∼ ≈ =
        ∑[ fun ∈ (ty ∼ → ty ≈) ]
        (ρ₁ ≈ ∘ fun ≡ ρ₁ ∼) × (ρ₂ ≈ ∘ fun ≡ ρ₂ ∼)


    FunRel : Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    FunRel-syntax : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    FunRel-syntax ∼ x₁ x₂ = ∼ x₁ x₂
    syntax FunRel-syntax ∼ x₁ x₂ = x₁ [ ∼ ] x₂

    ≡-FunRel : {X : Ty ℓ} →
        FunRel X
    ≡-FunRel = λ x₁ → λ x₂ → x₁ ≡ x₂


    FunRelMor : {X : Ty ℓ} →
        FunRel X → FunRel X → Ty ℓ
    FunRelMor {_} {X} ∼ ≈ =
        ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ [ ∼ ] x₂ → x₁ [ ≈ ] x₂)


    TyRel→FunRel : {X : Ty ℓ} →
        TyRel X → FunRel X
    TyRel→FunRel {_} {X} ∼ = λ x₁ → λ x₂ → x₁ ⟨ ∼ ⟩ x₂

    FunRel→TyRel : {X : Ty ℓ} →
        FunRel X → TyRel X
    FunRel→TyRel {_} {X} ∼ =
        (
            (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] x₁ [ ∼ ] x₂) ,
            pr₁ ,
            pr₁ ∘ pr₂
        )


    TyRel→FunRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ [ TyRel→FunRel ∼ ] x₂) ≡ (x₁ ⟨ ∼ ⟩ x₂)
    TyRel→FunRel-pres ∼ x₁ x₂ = refl

    FunRel→TyRel-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ ⟨ FunRel→TyRel ∼ ⟩ x₂) ≃ (x₁ [ ∼ ] x₂)
    FunRel→TyRel-pres {_} {X} ∼ x₁ x₂ =
        (
            (λ ((y₁ , y₂ , s) , p₁ , p₂) →
                tra (λ x → x [ ∼ ] x₂) p₁ (tra (λ y → y₁ [ ∼ ] y) p₂ s)
            ) ,
            Qinv→IsEqui (
                (λ s → ((x₁ , x₂ , s) , refl , refl)) ,
                (λ {((x₁ , x₂ , s) , refl , refl) → refl}) ,
                (λ s → refl)
            )
        )
