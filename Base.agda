{-# OPTIONS --without-K #-}


module M-types.Base where
    open import M-types.Ty public
    open import M-types.Sum public
    open import M-types.Prod public
    open import M-types.Eq public
    open import M-types.Equi public
    open import M-types.Contr public
    open import M-types.Rel public


    postulate
        funext-axiom : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {f₀ f₁ : ∏ X Y} →
            IsEqui {_} {_} {f₀ ≡ f₁} {∏[ x ∈ X ] f₀ x ≡ f₁ x} (≡-apply)

    funext :  {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {f₀ f₁ : ∏ X Y} →
        (∏[ x ∈ X ] f₀ x ≡ f₁ x) → f₀ ≡ f₁
    funext = inv (≡-apply , funext-axiom)
