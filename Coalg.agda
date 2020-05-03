{-# OPTIONS --without-K #-}

open import M-types.Ty

module Coalg {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import Coalg.Core A B
