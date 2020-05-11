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
    _⁻¹ : {X : Ty ℓ} {x₁ x₂ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₁
    refl ⁻¹ = refl

    infixr 9 _·_
    _·_ : {X : Ty ℓ} {x₁ x₂ x₃ : X} →
        x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
    refl · refl = refl


    ·-neutr₁ : {X : Ty ℓ} {x₁ x₂ : X} →
        ∏[ p ∈ x₁ ≡ x₂ ] refl · p ≡ p
    ·-neutr₁ refl = refl

    ·-neutr₂ : {X : Ty ℓ} {x₁ x₂ : X} →
        ∏[ p ∈ x₁ ≡ x₂ ] p · refl ≡ p
    ·-neutr₂ refl = refl


    infix 1 begin_
    begin_ : {X : Ty ℓ} {x₁ x₂ : X} →
        (x₁ ≡ x₂) → (x₁ ≡ x₂)
    begin p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : {X : Ty ℓ₁} {x₂ x₃ : X} →
        ∏[ x₁ ∈ X ] ((x₁ ≡ x₂) → (x₂ ≡ x₃) → (x₁ ≡ x₃))
    x₁ ≡⟨ p₁ ⟩ p₂ = p₁ · p₂

    infix 3 _∎
    _∎ : {X : Ty ℓ} →
        ∏[ x ∈ X ] x ≡ x
    x ∎ = refl


    tra : {X : Ty ℓ} {x₁ x₂ : X} →
        ∏[ Y ∈ (X → Ty ℓ₂) ] (x₁ ≡ x₂ → (Y x₁ → Y x₂))
    tra f refl = id

    tra-con : {X : Ty ℓ₁} {x₁ x₂ x₃ : X} →
        ∏[ Y ∈ (X → Ty ℓ₂) ] ∏[ p₁ ∈ x₁ ≡ x₂ ] ∏[ p₂ ∈ x₂ ≡ x₃ ]
        (tra Y p₂) ∘ (tra Y p₁) ≡ tra Y (p₁ · p₂)
    tra-con Y refl refl = refl


    ap : {X : Ty ℓ₁} {Y : Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (X → Y) ] ((x₁ ≡ x₂) → (f x₁ ≡ f x₂))
    ap f refl = refl

    ap-inv : {X : Ty ℓ₁} {Y : Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (X → Y) ] ∏[ p ∈ x₁ ≡ x₂ ] (ap f p)⁻¹ ≡ ap f (p ⁻¹)
    ap-inv f refl = refl


    apd : {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {x₁ x₂ : X} →
        ∏[ f ∈ (∏ X Y) ] ∏[ p ∈ x₁ ≡ x₂ ] tra Y p (f x₁) ≡ f x₂
    apd f refl = refl


    ≡-pair : {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {w₁ w₂ : ∑ X Y} →
        (∑[ p ∈ pr₁ w₁ ≡ pr₁ w₂ ] ((tra Y p (pr₂ w₁)) ≡ (pr₂ w₂))) → (w₁ ≡ w₂)
    ≡-pair (refl , refl) = refl

    ≡-apply : {X : Ty ℓ₁} {Y : X → Ty ℓ₂} {f₁ f₂ : ∏ X Y} →
        (f₁ ≡ f₂) → (∏[ x ∈ X ] (f₁ x ≡ f₂ x))
    ≡-apply refl = λ x → refl
