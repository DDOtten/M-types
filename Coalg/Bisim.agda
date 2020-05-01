{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.Bisim {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        ((Mor coalg C) × (Mor coalg C))

    coalg : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Coalg
    coalg {C} (coalg , p₁ , p₂) = coalg

    p₁ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    p₁ {C} (coalg , p₁ , p₂) = p₁

    p₂ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    p₂ {C} (coalg , p₁ , p₂) = p₂


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ rel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (rel c₁ c₂ → (Pbar rel) (obs C c₁) (obs C c₂))

    rel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] (ty C → ty C → Ty ℓ)
    rel (rel , bisim) = rel

    bisim : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (rel ∼ c₁ c₂ → (Pbar (rel ∼)) (obs C c₁) (obs C c₂))
    bisim (rel , bisim) = bisim


    funtra : {a₁ a₂ : A} {X : Ty ℓ} →
        ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₁ ∈ (B a₁ → X) ]
        (tra (λ a → (B a → X)) p f₁) ≡ (f₁ ∘ (tra B (sym p)))
    funtra refl f₁ = refl
