{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Rel where
    TyRel : {ℓ : Level} →
        Ty ℓ → Ty (ℓ-suc ℓ)
    TyRel {ℓ} X = ∑[ ty ∈ Ty ℓ ](ty → X) × (ty → X)

    ρ₁ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    ρ₁ (ty , ρ₁ , ρ₂) = ρ₁

    ρ₂ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    ρ₂ (ty , ρ₁ , ρ₂) = ρ₂

    TyRel-syntax : {ℓ : Level} →
        ∏[ X ∈ Ty ℓ ] ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    TyRel-syntax X ∼ x₁ x₂ = ∑[ s ∈ (ty ∼) ] ((ρ₁ ∼ s ≡ x₁) × (ρ₂ ∼ s ≡ x₂))
    syntax TyRel-syntax X ∼ x₁ x₂ = x₁ ⟨ X / ∼ ⟩ x₂


    FunRel : {ℓ : Level} →
        Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    FunRel-syntax : {ℓ : Level} →
        ∏[ X ∈ Ty ℓ ] ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] Ty ℓ
    FunRel-syntax X ∼ x₁ x₂ = ∼ x₁ x₂
    syntax FunRel-syntax X ∼ x₁ x₂ = x₁ [ X / ∼ ] x₂


    tyToFun : {ℓ : Level} {X : Ty ℓ} →
        TyRel X → FunRel X
    tyToFun {ℓ} {X} ∼ = λ x₁ → λ x₂ → x₁ ⟨ X / ∼ ⟩ x₂

    funToTy : {ℓ : Level} {X : Ty ℓ} →
        FunRel X → TyRel X
    funToTy {ℓ} {X} ∼ =
        (
            (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] x₁ [ X / ∼ ] x₂) ,
            pr₁ ,
            pr₁ ∘ pr₂
        )


    tyToFunPres : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ [ X / tyToFun ∼ ] x₂) ≡ (x₁ ⟨ X / ∼ ⟩ x₂)
    tyToFunPres ∼ x₁ x₂ = refl

    funToTyPres : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ]
        (x₁ ⟨ X / funToTy ∼ ⟩ x₂) ≃ (x₁ [ X / ∼ ] x₂)
    funToTyPres {ℓ} {X} ∼ x₁ x₂ =
        (
            (λ ((y₁ , y₂ , s) , p₁ , p₂) →
                tra (λ x → x [ X / ∼ ] x₂) p₁ (tra (λ y → y₁ [ X / ∼ ] y) p₂ s)
            ) ,
            (
                (λ s → ((x₁ , x₂ , s) , refl , refl)) ,
                (λ {((x₁ , x₂ , s) , refl , refl) → refl})
            ) ,
            (
                (λ s → ((x₁ , x₂ , s) , refl , refl)) ,
                (λ s → refl)
            )
        )
