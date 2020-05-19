{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Rel where
    TyRel : Ty ℓ → Ty (ℓ-suc ℓ)
    TyRel {ℓ} X = ∑[ ty ∈ Ty ℓ ] (ty → X) × (ty → X)

    ρ₁ : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    ρ₁ (_ , ρ₁ , _) = ρ₁

    ρ₂ : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    ρ₂ (_ , _ , ρ₂) = ρ₂

    TyRel-syntax : ∏[ X ∈ Ty ℓ ] ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    TyRel-syntax X ∼ x₁ x₂ = ∑[ s ∈ (ty ∼) ] ((ρ₁ ∼ s ≡ x₁) × (ρ₂ ∼ s ≡ x₂))
    syntax TyRel-syntax X ∼ x₁ x₂ = x₁ ⟨ X / ∼ ⟩ x₂


    FunRel : Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    FunRel-syntax : ∏[ X ∈ Ty ℓ ] ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    FunRel-syntax X ∼ x₁ x₂ = ∼ x₁ x₂
    syntax FunRel-syntax X ∼ x₁ x₂ = x₁ [ X / ∼ ] x₂


    Ty→Fun : {X : Ty ℓ} →
        TyRel X → FunRel X
    Ty→Fun {_} {X} ∼ = λ x₁ → λ x₂ → x₁ ⟨ X / ∼ ⟩ x₂

    Fun→Ty : {X : Ty ℓ} →
        FunRel X → TyRel X
    Fun→Ty {_} {X} ∼ =
        (
            (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] x₁ [ X / ∼ ] x₂) ,
            pr₁ ,
            pr₁ ∘ pr₂
        )


    Ty→Fun-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ [ X / Ty→Fun ∼ ] x₂) ≡ (x₁ ⟨ X / ∼ ⟩ x₂)
    Ty→Fun-pres ∼ x₁ x₂ = refl

    Fun→Ty-pres : {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ ⟨ X / Fun→Ty ∼ ⟩ x₂) ≃ (x₁ [ X / ∼ ] x₂)
    Fun→Ty-pres {_} {X} ∼ x₁ x₂ =
        (
            (λ ((y₁ , y₂ , s) , p₁ , p₂) →
                tra (λ x → x [ X / ∼ ] x₂) p₁ (tra (λ y → y₁ [ X / ∼ ] y) p₂ s)
            ) ,
            Qinv→IsEqui (
                (λ s → ((x₁ , x₂ , s) , refl , refl)) ,
                (λ {((x₁ , x₂ , s) , refl , refl) → refl}) ,
                (λ s → refl)
            )
        )
