{-# OPTIONS --without-K #-}


module M-types.Base where
    open import M-types.Ty public
    open import M-types.Equality public
    open import M-types.Sum public
    open import M-types.Prod public
    open import M-types.Equivalence public


    id : {ℓ : Level} {X : Ty ℓ} →
        (X → X)
    id x = x

    infixr 9 _∘_
    _∘_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {Z : {x : X} → Y x → Ty ℓ₃} →
        ∏[ g ∈ ({x : X} → ∏[ y ∈ Y x ] Z y) ]
        ∏[ f ∈ (∏[ x ∈ X ] Y x) ]
        ∏[ x ∈ X ] Z (f x)
    f ∘ g = λ x → f (g x)


    infix 1 begin_
    begin_ : {ℓ : Level} {X : Ty ℓ} {x₁ x₂ : X} →
        (x₁ ≡ x₂) → (x₁ ≡ x₂)
    begin p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : {ℓ : Level} {X : Ty ℓ} {x₂ x₃ : X} →
        ∏[ x₁ ∈ X ] ((x₁ ≡ x₂) → (x₂ ≡ x₃) → (x₁ ≡ x₃))
    x₁ ≡⟨ p₁ ⟩ p₂ = p₁ · p₂

    infix 3 _∎
    _∎ : {ℓ : Level} {X : Ty ℓ} →
        ∏[ x ∈ X ] x ≡ x
    x ∎ = refl


    tra : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {x₁ x₂ : X} →
        (Y : X → Ty ℓ₂) → x₁ ≡ x₂ → (Y x₁ → Y x₂)
    tra f refl = id

    ap : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (X → Y) ] ((x₁ ≡ x₂) → (f x₁ ≡ f x₂))
    ap f refl = refl

    apInv : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (X → Y) ] ∏[ p ∈ x₁ ≡ x₂ ] (ap f p)⁻¹ ≡ ap f (p ⁻¹)
    apInv f refl = refl

    apd : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (∏ X Y) ] ∏[ p ∈ x₁ ≡ x₂ ] tra Y p (f x₁) ≡ f x₂
    apd f refl = refl

    traCon : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {x₁ x₂ x₃ : X} →
        ∏[ p₁ ∈ x₁ ≡ x₂ ] ∏[ p₂ ∈ x₂ ≡ x₃ ] ((tra Y p₂) ∘ (tra Y p₁) ≡ (tra Y (p₁ · p₂)))
    traCon refl refl = refl


    ≡-pair : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {w₁ w₂ : ∑ X Y} →
        (∑[ p ∈ pr₁ w₁ ≡ pr₁ w₂ ] ((tra Y p (pr₂ w₁)) ≡ (pr₂ w₂))) → (w₁ ≡ w₂)
    ≡-pair (refl , refl) = refl

    ≡-apply : {ℓ₁ ℓ₂ : Level} {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {f₁ f₂ : ∏ X Y} →
        (f₁ ≡ f₂) → ∏[ x ∈ X ] (f₁ x ≡ f₂ x)
    ≡-apply refl = λ x → refl


    ty = pr₁
    fun = pr₁
