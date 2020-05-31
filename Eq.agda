{-# OPTIONS --without-K #-}


open import M-types.Ty
open import M-types.Sum
open import M-types.Prod


module M-types.Eq where
    infix 4 _≡_
    data _≡_ {X : Ty ℓ} : X → X → Ty ℓ where
        refl : {x : X} → x ≡ x
    open _≡_ public

    infix 10 _⁻¹
    _⁻¹ : {X : Ty ℓ} {x₀ x₁ : X} →
        x₀ ≡ x₁ → x₁ ≡ x₀
    refl ⁻¹ = refl

    infixr 9 _·_
    _·_ : {X : Ty ℓ} {x₀ x₁ x₂ : X} →
        x₀ ≡ x₁ → x₁ ≡ x₂ → x₀ ≡ x₂
    refl · refl = refl


    ·-neutr₀ : {X : Ty ℓ} {x₀ x₁ : X} →
        ∏[ p ∈ x₀ ≡ x₁ ] refl · p ≡ p
    ·-neutr₀ refl = refl

    ·-neutr₁ : {X : Ty ℓ} {x₀ x₁ : X} →
        ∏[ p ∈ x₀ ≡ x₁ ] p · refl ≡ p
    ·-neutr₁ refl = refl


    infix 1 begin_
    begin_ : {X : Ty ℓ} {x₀ x₁ : X} →
        (x₀ ≡ x₁) → (x₀ ≡ x₁)
    begin p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : {X : Ty ℓ₀} {x₁ x₂ : X} →
        ∏[ x₀ ∈ X ] ((x₀ ≡ x₁) → (x₁ ≡ x₂) → (x₀ ≡ x₂))
    x₀ ≡⟨ p₀ ⟩ p₁ = p₀ · p₁

    infix 3 _∎
    _∎ : {X : Ty ℓ} →
        ∏[ x ∈ X ] x ≡ x
    x ∎ = refl


    tra : {X : Ty ℓ} {x₀ x₁ : X} →
        ∏[ Y ∈ (X → Ty ℓ₁) ] (x₀ ≡ x₁ → (Y x₀ → Y x₁))
    tra f refl = id

    tra-con : {X : Ty ℓ₀} {x₀ x₁ x₂ : X} →
        ∏[ Y ∈ (X → Ty ℓ₁) ] ∏[ p₀ ∈ x₀ ≡ x₁ ] ∏[ p₁ ∈ x₁ ≡ x₂ ]
        (tra Y p₁) ∘ (tra Y p₀) ≡ tra Y (p₀ · p₁)
    tra-con Y refl refl = refl


    ap : {X : Ty ℓ₀} {Y : Ty ℓ₁} {x₀ x₁ : X} →
        ∏[ f ∈ (X → Y) ] ((x₀ ≡ x₁) → (f x₀ ≡ f x₁))
    ap f refl = refl

    ap-inv : {X : Ty ℓ₀} {Y : Ty ℓ₁} {x₀ x₁ : X} →
        ∏[ f ∈ (X → Y) ] ∏[ p ∈ x₀ ≡ x₁ ] (ap f p)⁻¹ ≡ ap f (p ⁻¹)
    ap-inv f refl = refl


    apd : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {x₀ x₁ : X} →
        ∏[ f ∈ (∏ X Y) ] ∏[ p ∈ x₀ ≡ x₁ ] tra Y p (f x₀) ≡ f x₁
    apd f refl = refl


    ≡-pair : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {w₀ w₁ : ∑ X Y} →
        (∑[ p ∈ pr₀ w₀ ≡ pr₀ w₁ ] ((tra Y p (pr₁ w₀)) ≡ (pr₁ w₁))) → (w₀ ≡ w₁)
    ≡-pair (refl , refl) = refl

    ≡-apply : {X : Ty ℓ₀} {Y : X → Ty ℓ₁} {f₀ f₁ : ∏ X Y} →
        (f₀ ≡ f₁) → (∏[ x ∈ X ] (f₀ x ≡ f₁ x))
    ≡-apply refl = λ x → refl
