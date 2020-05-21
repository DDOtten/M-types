{-# OPTIONS --without-K #-}


open import M-types.Base
import M-types.Rel


module M-types.Coalg.Bisim (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        (Mor coalg C) × (Mor coalg C)

    tyRel : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] M-types.Rel.TyRel (ty C)
    tyRel (coalg , ρ₁ , ρ₂) = (ty coalg , fun ρ₁ , fun ρ₂)

    coalg : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Coalg
    coalg (coalg , _ , _) = coalg

    ρ₁ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₁ (_ , ρ₁ , _) = ρ₁

    ρ₂ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₂ (_ , _ , ρ₂) = ρ₂

    P-TyBisim : {C : Coalg} →
        TyBisim C → TyBisim (P-coalg C)
    P-TyBisim {C} ∼ =
        (
            P-coalg (coalg {C} ∼) ,
            P-mor {coalg {C} ∼} {C} (ρ₁ {C} ∼) ,
            P-mor {coalg {C} ∼} {C} (ρ₂ {C} ∼)
        )

    TyBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    TyBisim-syntax C ∼ c₁ c₂ =
        M-types.Rel.TyRel-syntax (ty C) (tyRel {C} ∼) c₁ c₂
    syntax TyBisim-syntax C ∼ c₁ c₂ = c₁ ⟨ C / ∼ ⟩ c₂


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ funRel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (funRel c₁ c₂ → (P-FunRel funRel) (obs C c₁) (obs C c₂))

    funRel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] M-types.Rel.FunRel (ty C)
    funRel (funRel , _) = funRel

    P-FunBisim : {C : Coalg} →
        FunBisim C → FunBisim (P-coalg C)
    P-FunBisim {C} ∼ =
        (
            P-FunRel (funRel ∼) ,
            λ (a , d₁) → λ (a , d₂) → λ {(refl , e) → (
                refl ,
                λ b → pr₂ ∼ (d₁ b) (d₂ b) (e b)
            )}
        )

    FunBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    FunBisim-syntax C ∼ c₁ c₂ =
        M-types.Rel.FunRel-syntax (ty C) (funRel ∼) c₁ c₂
    syntax FunBisim-syntax C ∼ c₁ c₂ = c₁ [ C / ∼ ] c₂

    funBisim : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ C / ∼ ] c₂ → obs C c₁ [ P-coalg C / P-FunBisim {C} ∼ ] obs C c₂)
    funBisim (_ , funBisim) = funBisim


    Ty→Fun : {C : Coalg} →
        TyBisim C → FunBisim C
    Ty→Fun {C} ∼ =
        (
            (λ c₁ → λ c₂ → c₁ ⟨ C / ∼ ⟩ c₂) ,
            (λ c₁ → λ c₂ → λ (s , p₁ , p₂) → let
                q₁ = begin
                        obs C c₁
                    ≡⟨ ap (obs C) (p₁ ⁻¹) ⟩
                        obs C (fun (ρ₁ {C} ∼) s)
                    ≡⟨ ≡-apply (com {coalg {C} ∼} {C} (ρ₁ {C} ∼)) s ⟩
                        (
                            pr₁ (obs (coalg {C} ∼) s) ,
                            fun (ρ₁ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s)
                        )
                    ∎
                q₂ = begin
                        obs C c₂
                    ≡⟨ ap (obs C) (p₂ ⁻¹) ⟩
                        obs C (fun (ρ₂ {C} ∼) s)
                    ≡⟨ ≡-apply (com {coalg {C} ∼} {C} (ρ₂ {C} ∼)) s ⟩
                        (
                            pr₁ (obs (coalg {C} ∼) s) ,
                            fun (ρ₂ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s)
                        )
                    ∎
            in (
                (ap pr₁ q₁) · (ap pr₁ q₂)⁻¹ ,
                (λ b₁ → (
                    pr₂ (obs (coalg {C} ∼) s) (tra B (ap pr₁ q₁) b₁),
                    (apply-pr₂ q₁ b₁)⁻¹ ,
                    (apply-pr₂ (q₂ ⁻¹) (tra B (ap pr₁ q₁) b₁)) ·
                    ap (pr₂ (obs C c₂)) (≡-apply (
                        tra-con B (ap pr₁ q₁) (ap pr₁ (q₂ ⁻¹)) ·
                        (ap (λ r → tra B (ap pr₁ q₁ · r)) ((ap-inv pr₁ q₂)⁻¹))
                    ) b₁)
                ))
            ))
        ) where
            apply-pr₂ : {(a₁ , d₁) (a₂ , d₂) : P-Ty (ty C)} →
                ∏[ p ∈ (a₁ , d₁) ≡ (a₂ , d₂) ] ∏[ b₁ ∈ B a₁ ]
                d₁ b₁ ≡ d₂ (tra B (ap pr₁ p) b₁)
            apply-pr₂ refl b = refl

    Fun→Ty : {C : Coalg} →
        FunBisim C → TyBisim C
    Fun→Ty {C} ∼ =
        (
            (
                (∑[ c₁ ∈ ty C ] ∑[ c₂ ∈ ty C ] c₁ [ C / ∼ ] c₂) ,
                (λ (c₁ , c₂ , s) → (
                    pr₁ (obs C c₁) ,
                    λ b₁ → (
                        pr₂ (obs C c₁) b₁ ,
                        pr₂ (obs C c₂) (tra B (pr₁ (funBisim ∼ c₁ c₂ s)) b₁) ,
                        pr₂ (funBisim ∼ c₁ c₂ s) b₁
                    )
                ))
            ) ,
            (
                pr₁ ,
                funext (λ (c₁ , c₂ , s) → ≡-pair (
                    refl ,
                    refl
                ))
            ) ,
            (
                (pr₁ ∘ pr₂) ,
                funext (λ (c₁ , c₂ , s) → ≡-pair (
                    (pr₁ (funBisim ∼ c₁ c₂ s)) ,
                    fun-tra (pr₁ (funBisim ∼ c₁ c₂ s)) (pr₂ (obs C c₂))
                )⁻¹)
            )
        ) where
            fun-tra : {a₁ a₂ : A} {X : Ty ℓ} →
                ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₂ ∈ (B a₂ → X) ]
                tra (λ a → (B a → X)) p (f₂ ∘ (tra B p)) ≡ f₂
            fun-tra refl f₂ = refl


    Ty→Fun-pres : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ C / Ty→Fun {C} ∼ ] c₂) ≡ (c₁ ⟨ C / ∼ ⟩ c₂)
    Ty→Fun-pres {C} ∼ c₁ c₂ = M-types.Rel.Ty→Fun-pres (tyRel {C} ∼) c₁ c₂

    Fun→Ty-pres : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ ⟨ C / Fun→Ty {C} ∼ ⟩ c₂) ≃ (c₁ [ C / ∼ ] c₂)
    Fun→Ty-pres ∼ c₁ c₂ = M-types.Rel.Fun→Ty-pres (funRel ∼) c₁ c₂
