{-# OPTIONS --without-K #-}


module M-types.Base where
    open import M-types.Ty public
    open import M-types.Sum public
    open import M-types.Prod public
    open import M-types.Eq public
    open import M-types.Equi public
    open import M-types.Contr public


    postulate
        funext : {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {f₁ f₂ : ∏ X Y} →
            IsEqui {_} {_} {f₁ ≡ f₂} {∏[ x ∈ X ] (f₁ x ≡ f₂ x)} (≡-apply)
