{-# OPTIONS --without-K #-}

module M-types.ty where
    open import Agda.Primitive public using (Level) renaming (
        lzero to ℓ-zero ;
        lsuc to ℓ-suc ;
        _⊔_ to ℓ-max )

    Ty : (ℓ : Level) → Set (ℓ-suc ℓ)
    Ty ℓ = Set ℓ
