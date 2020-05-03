{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Rel where
    TyRel : {ℓ : Level} →
        Ty ℓ → Ty (ℓ-suc ℓ)
    TyRel {ℓ} X = ∑[ ty ∈ Ty ℓ ](ty → X) × (ty → X)

    p₁ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    p₁ (ty , p₁ , p₂) = p₁

    p₂ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    p₂ (ty , p₁ , p₂) = p₂


    FunRel : {ℓ : Level} →
        Ty ℓ → Ty (ℓ-suc ℓ)
    FunRel {ℓ} X = X → X → Ty ℓ


    tyToFun : {ℓ : Level} {X : Ty ℓ} →
        TyRel X → FunRel X
    tyToFun {ℓ} {X} ∼ = λ x₁ → λ x₂ →
        ∑[ s ∈ (ty ∼) ] ((p₁ ∼ s ≡ x₁) × (p₂ ∼ s ≡ x₂))

    funToTy : {ℓ : Level} {X : Ty ℓ} →
        FunRel X → TyRel X
    funToTy {ℓ} {X} ∼ =
        (
            (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] ∼ x₁ x₂) ,
            pr₁ ,
            pr₁ ∘ pr₂
        )
