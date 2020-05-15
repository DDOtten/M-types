{-# OPTIONS --without-K #-}

open import M-types.Ty
open import M-types.Sum
open import M-types.Prod
open import M-types.Eq


module M-types.Contr where
    IsContr : ∏[ X ∈ Ty ℓ ] Ty ℓ
    IsContr X = ∑[ x ∈ X ] ∏[ x′ ∈ X ] x′ ≡ x

    Contr : Ty (ℓ-suc ℓ)
    Contr {ℓ} = ∑[ X ∈ Ty ℓ ] IsContr X
