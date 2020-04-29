{-# OPTIONS --without-K #-}

open import Agda.Primitive

module M-types.product where
    ∏ : {a b : Level} → (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
    ∏ A B = (a : A) → B a

    ∏-syntax = ∏
    infix 2 ∏-syntax
    syntax ∏-syntax A (λ a → B) = ∏[ a ∈ A ] B
