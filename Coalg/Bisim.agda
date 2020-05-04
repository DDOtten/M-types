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

    funtra' : {a₁ a₂ : A} {X : Ty ℓ} →
        ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₁ ∈ (B a₂ → X) ]
        tra (λ a → (B a → X)) (p ⁻¹) f₁ ≡ f₁ ∘ (tra B p)
    funtra' refl f₁ = refl

    tyToFun : {C : Coalg} →
        TyBisim C → FunBisim C
    tyToFun {C} ∼ =
        (
            (λ c₁ → λ c₂ → ∑[ s ∈ (ty (coalg {C} ∼)) ]
                ((fun (ρ₁ {C} ∼) s ≡ c₁) × (fun (ρ₂ {C} ∼) s ≡ c₂))
            ) ,
            (λ c₁ → λ c₂ → λ (s , p₁ , p₂) →
                let
                    q₁ = begin
                            obs C c₁
                        ≡⟨ ap (obs C) (p₁ ⁻¹) ⟩
                            obs C (fun (ρ₁ {C} ∼) s)
                        ≡⟨ com {coalg {C} ∼} {C} (ρ₁ {C} ∼) s ⟩
                            (pr₁ (obs (coalg {C} ∼) s) , fun (ρ₁ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s))
                        ∎
                    q₂ = begin
                            obs C c₂
                        ≡⟨ ap (obs C) (p₂ ⁻¹) ⟩
                            obs C (fun (ρ₂ {C} ∼) s)
                        ≡⟨ com {coalg {C} ∼} {C} (ρ₂ {C} ∼) s ⟩
                            (pr₁ (obs (coalg {C} ∼) s) , fun (ρ₂ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s))
                        ∎
                in
                    (ap pr₁ q₁) · ((ap pr₁ q₂)⁻¹) ,
                    (λ b₁ → (
                        pr₂ (obs (coalg {C} ∼) s) (tra B (ap pr₁ q₁) b₁),
                        (r₁ q₁ b₁)⁻¹ ,
                        (r₁ (q₂ ⁻¹) (tra B (ap pr₁ q₁) b₁)) ·
                        ap (pr₂ (obs C c₂)) (≡-apply (tracon {ℓ} {ℓ} {A} {B} (ap pr₁ q₁) (ap pr₁ (q₂ ⁻¹)) · (ap (λ r → tra B (ap pr₁ q₁ · r)) ((apInv pr₁ q₂)⁻¹))) b₁)
                    ))
            )
        ) where
            r₁ : {pc₁ pc₂ : P (ty C)} →
                ∏[ p ∈ (pc₁ ≡ pc₂) ] ∏[ b₁ ∈ B (pr₁ pc₁) ] (pr₂ pc₁ b₁ ≡ pr₂ pc₂ (tra B (ap pr₁ p) b₁))
            r₁ refl b = refl



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
