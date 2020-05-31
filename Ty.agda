{-# OPTIONS --without-K #-}


module M-types.Ty where
    open import Agda.Primitive public using (Level) renaming
        (
            lzero to ℓ-zero ;
            lsuc to ℓ-suc ;
            _⊔_ to ℓ-max
        )

    variable
        ℓ ℓ₀ ℓ₁ ℓ₂ : Level


    Ty : (ℓ : Level) → Set (ℓ-suc ℓ)
    Ty ℓ = Set ℓ
