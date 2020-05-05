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

    _⟨_⟩_ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ x₁ ∈ X ] ∏[ ∼ ∈ TyRel X ] ∏[ x₂ ∈ X ] Ty ℓ
    x₁ ⟨ ∼ ⟩ x₂ = ∑[ s ∈ (ty ∼) ] ((ρ₁ ∼ s ≡ x₁) × (ρ₂ ∼ s ≡ x₂))


    FunRel : {ℓ : Level} →
        Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ

    _[_]_ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ x₁ ∈ X ] ∏[ ∼ ∈ FunRel X ] ∏[ x₂ ∈ X ] Ty ℓ
    x₁ [ ∼ ] x₂ = ∼ x₁ x₂


    tyToFun : {ℓ : Level} {X : Ty ℓ} →
        TyRel X → FunRel X
    tyToFun {ℓ} {X} ∼ = λ x₁ → λ x₂ → x₁ ⟨ ∼ ⟩ x₂

    funToTy : {ℓ : Level} {X : Ty ℓ} →
        FunRel X → TyRel X
    funToTy {ℓ} {X} ∼ =
        (
            (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] x₁ [ ∼ ] x₂) ,
            pr₁ ,
            pr₁ ∘ pr₂
        )


    tyToFunPres : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] (x₁ [ tyToFun ∼ ] x₂) ≡ (x₁ ⟨ ∼ ⟩ x₂)
    tyToFunPres ∼ x₁ x₂ = refl

    funToTyPres : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ FunRel X ] ∏[ x₁ ∈ X ] ∏[ x₂ ∈ X ] (x₁ ⟨ funToTy ∼ ⟩ x₂) ≃ (x₁ [ ∼ ] x₂)
    funToTyPres ∼ x₁ x₂ =
        (
            (λ ((y₁ , y₂ , s) , p₁ , p₂) →
                tra (λ x → x [ ∼ ] x₂) p₁ (tra (λ y → y₁ [ ∼ ] y) p₂ s)
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
