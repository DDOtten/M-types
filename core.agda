{-# OPTIONS --without-K #-}

module M-types.core where
    open import M-types.equality public
    open import M-types.sum public
    open import M-types.product public


    Ty = Set
    Ty₀ = Set₀
    Ty₁ = Set₁
    Ty₂ = Set₂

    ty = pr₁
    fun = pr₁

    _∘_ : {X Y Z : Ty} → (Y → Z) → (X → Y) → (X → Z)
    g ∘ f = λ x → g (f x)
