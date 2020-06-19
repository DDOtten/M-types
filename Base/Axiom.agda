{-# OPTIONS --without-K #-}


module M-types.Base.Axiom where
    open import M-types.Base.Core public
    open import M-types.Base.Sum public
    open import M-types.Base.Prod public
    open import M-types.Base.Eq public
    open import M-types.Base.Equi public


    postulate
        funext-axiom : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {f₀ f₁ : ∏ X Y} →
            IsEqui {_} {_} {f₀ ≡ f₁} {∏[ x ∈ X ] f₀ x ≡ f₁ x} (≡-apply)

    funext :  {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {f₀ f₁ : ∏ X Y} →
        (∏[ x ∈ X ] f₀ x ≡ f₁ x) → f₀ ≡ f₁
    funext = inv (≡-apply , funext-axiom)
