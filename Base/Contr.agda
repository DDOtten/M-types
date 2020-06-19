{-# OPTIONS --without-K #-}

open import M-types.Base.Core
open import M-types.Base.Sum
open import M-types.Base.Prod
open import M-types.Base.Eq


module M-types.Base.Contr where
    IsContr : ∏[ X ∈ Ty ℓ ] Ty ℓ
    IsContr X = ∑[ x ∈ X ] ∏[ x′ ∈ X ] x′ ≡ x

    Contr : Ty (ℓ-suc ℓ)
    Contr {ℓ} = ∑[ X ∈ Ty ℓ ] IsContr X
