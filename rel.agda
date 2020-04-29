{-# OPTIONS --without-K #-}

open import M-types.core

module M-types.rel (A : Ty) (B : A → Ty) where
    open import M-types.coalg A B

    open import Agda.Primitive


    TyRel : Ty → Ty₁
    TyRel X = ∑[ ty ∈ Ty ](ty → X) × (ty → X)

    p₁ : {X : Ty} → ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    p₁ (ty , p₁ , p₂) = p₁

    p₂ : {X : Ty} → ∏[ ∼ ∈ TyRel X ] (ty ∼ → X)
    p₂ (ty , p₁ , p₂) = p₂


    FunRel : Ty → Ty₁
    FunRel X = X → X → Ty


    tyToFun : {X : Ty} → TyRel X → FunRel X
    tyToFun {X} ∼ = λ x₁ → λ x₂ → ∑[ s ∈ (ty ∼) ] ((p₁ ∼ s ≡ x₁) × (p₂ ∼ s ≡ x₂))

    funToTy : {X : Ty} → FunRel X → TyRel X
    funToTy {X} ∼ =
        (∑[ x₁ ∈ X ] ∑[ x₂ ∈ X ] ∼ x₁ x₂) ,
        (λ (x₁ , x₂ , s) → x₁) ,
        (λ (x₁ , x₂ , s) → x₂)
