{-# OPTIONS --without-K #-}

module M-types.core where
    Ty = Set
    Ty₀ = Set₀
    Ty₁ = Set₁
    Ty₂ = Set₂

    _∘_ : {X Y Z : Ty} → (Y → Z) → (X → Y) → (X → Z)
    g ∘ f = λ x → g (f x)
