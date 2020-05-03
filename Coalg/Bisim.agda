{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.Bisim {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        ((Mor coalg C) × (Mor coalg C))

    coalg : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Coalg
    coalg {C} (coalg , ρ₁ , ρ₂) = coalg

    ρ₁ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₁ {C} (coalg , ρ₁ , ρ₂) = ρ₁

    ρ₂ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₂ {C} (coalg , ρ₁ , ρ₂) = ρ₂


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
        ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₂ ∈ (B a₂ → X) ]
        tra (λ a → (B a → X)) p (f₂ ∘ (tra B p)) ≡ f₂
    funtra refl f₂ = refl


    tyToFun : {C : Coalg} →
        TyBisim C → FunBisim C
    tyToFun {C} ∼ =
        (
            (λ c₁ → λ c₂ → ∑[ s ∈ (ty (coalg {C} ∼)) ]
                ((fun (ρ₁ {C} ∼) s ≡ c₁) × (fun (ρ₂ {C} ∼) s ≡ c₂))
            ) ,
            (λ c₁ → λ c₂ → λ (s , p₁ , p₂) → (
                (ap (pr₁) (ap (obs C) (p₁ ⁻¹) · com {coalg {C} ∼} {C} (ρ₁ {C} ∼) s)) ·
                (ap (pr₁) (ap (obs C) (p₂ ⁻¹) · com {coalg {C} ∼} {C} (ρ₂ {C} ∼) s))⁻¹ ,
                (λ b₁ → (
                    pr₂ (obs (coalg {C} ∼) s) (tra
                        B
                        (ap (pr₁) (ap (obs C) (p₁ ⁻¹) · com {coalg {C} ∼} {C} (ρ₁ {C} ∼) s))
                        b₁
                    ),
                    ≡-apply {!   !} b₁ ,
                    {!   !}
                ))
            ))
        )


    funToTy : {C : Coalg} →
        FunBisim C → TyBisim C
    funToTy {C} ∼ =
        (
            (
                (∑[ c₁ ∈ ty C ] ∑[ c₂ ∈ ty C ] rel ∼ c₁ c₂) ,
                (λ (c₁ , c₂ , s) → (
                    pr₁ (obs C c₁) ,
                    λ b₁ → (
                        pr₂ (obs C c₁) b₁ ,
                        pr₂ (obs C c₂) (tra B (pr₁ (bisim ∼ c₁ c₂ s)) b₁) ,
                        pr₂ (bisim ∼ c₁ c₂ s) b₁
                    )
                ))
            ) ,
            (
                pr₁ ,
                (λ (c₁ , c₂ , s) → ≡-pair (
                    refl ,
                    refl
                ))
            ) ,
            (
                (pr₁ ∘ pr₂) ,
                (λ (c₁ , c₂ , s) → ≡-pair (
                    (pr₁ (bisim ∼ c₁ c₂ s)) ,
                    funtra (pr₁ (bisim ∼ c₁ c₂ s)) (pr₂ (obs C c₂))
                )⁻¹)
            )
        )
