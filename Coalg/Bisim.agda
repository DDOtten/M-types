{-# OPTIONS --without-K #-}


open import M-types.Base
import M-types.Rel


module M-types.Coalg.Bisim {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        ((Mor coalg C) × (Mor coalg C))

    tyRel : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] M-types.Rel.TyRel (ty C)
    tyRel (coalg , ρ₁ , ρ₂) = (ty coalg , fun ρ₁ , fun ρ₂)

    coalg : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Coalg
    coalg {C} (coalg , ρ₁ , ρ₂) = coalg

    ρ₁ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₁ {C} (coalg , ρ₁ , ρ₂) = ρ₁

    ρ₂ : {C : Coalg} → ∏[ ∼ ∈ TyBisim C ] Mor (coalg {C} ∼) C
    ρ₂ {C} (coalg , ρ₁ , ρ₂) = ρ₂

    TyBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    TyBisim-syntax C ∼ c₁ c₂ = M-types.Rel.TyRel-syntax (ty C) (tyRel {C} ∼) c₁ c₂
    syntax TyBisim-syntax C ∼ c₁ c₂ = c₁ ⟨ C / ∼ ⟩ c₂


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ rel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (rel c₁ c₂ → (Pbar rel) (obs C c₁) (obs C c₂))

    funRel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] M-types.Rel.FunRel (ty C)
    funRel (funRel , bisim) = funRel

    bisim : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (funRel ∼ c₁ c₂ → (Pbar (funRel ∼)) (obs C c₁) (obs C c₂))
    bisim (funRel , bisim) = bisim

    FunBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    FunBisim-syntax C ∼ c₁ c₂ = M-types.Rel.FunRel-syntax (ty C) (funRel ∼) c₁ c₂
    syntax FunBisim-syntax C ∼ c₁ c₂ = c₁ [ C / ∼ ] c₂


    tyToFun : {C : Coalg} →
        TyBisim C → FunBisim C
    tyToFun {C} ∼ =
        (
            (λ c₁ → λ c₂ → c₁ ⟨ C / ∼ ⟩ c₂) ,
            (λ c₁ → λ c₂ → λ (s , p₁ , p₂) →
                let
                    q₁ = begin
                            obs C c₁
                        ≡⟨ ap (obs C) (p₁ ⁻¹) ⟩
                            obs C (fun (ρ₁ {C} ∼) s)
                        ≡⟨ com {coalg {C} ∼} {C} (ρ₁ {C} ∼) s ⟩
                            (
                                pr₁ (obs (coalg {C} ∼) s) ,
                                fun (ρ₁ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s)
                            )
                        ∎
                    q₂ = begin
                            obs C c₂
                        ≡⟨ ap (obs C) (p₂ ⁻¹) ⟩
                            obs C (fun (ρ₂ {C} ∼) s)
                        ≡⟨ com {coalg {C} ∼} {C} (ρ₂ {C} ∼) s ⟩
                            (
                                pr₁ (obs (coalg {C} ∼) s) ,
                                fun (ρ₂ {C} ∼) ∘ pr₂ (obs (coalg {C} ∼) s)
                            )
                        ∎
                in
                    (ap pr₁ q₁) · ((ap pr₁ q₂)⁻¹) ,
                    (λ b₁ → (
                        pr₂ (obs (coalg {C} ∼) s) (tra B (ap pr₁ q₁) b₁),
                        (applyPr₂ q₁ b₁)⁻¹ ,
                        (applyPr₂ (q₂ ⁻¹) (tra B (ap pr₁ q₁) b₁)) ·
                        ap (pr₂ (obs C c₂)) (≡-apply (
                            traCon {ℓ} {ℓ} {A} {B} (ap pr₁ q₁) (ap pr₁ (q₂ ⁻¹)) ·
                            (ap (λ r → tra B (ap pr₁ q₁ · r)) ((apInv pr₁ q₂)⁻¹))
                        ) b₁)
                    ))
            )
        ) where
            applyPr₂ : {pc₁ pc₂ : P (ty C)} →
                ∏[ p ∈ (pc₁ ≡ pc₂) ] ∏[ b₁ ∈ B (pr₁ pc₁) ]
                pr₂ pc₁ b₁ ≡ pr₂ pc₂ (tra B (ap pr₁ p) b₁)
            applyPr₂ refl b = refl

    funToTy : {C : Coalg} →
        FunBisim C → TyBisim C
    funToTy {C} ∼ =
        (
            (
                (∑[ c₁ ∈ ty C ] ∑[ c₂ ∈ ty C ] c₁ [ C / ∼ ] c₂) ,
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
                    funTra (pr₁ (bisim ∼ c₁ c₂ s)) (pr₂ (obs C c₂))
                )⁻¹)
            )
        ) where
            funTra : {a₁ a₂ : A} {X : Ty ℓ} →
                ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₂ ∈ (B a₂ → X) ]
                tra (λ a → (B a → X)) p (f₂ ∘ (tra B p)) ≡ f₂
            funTra refl f₂ = refl


    tyToFunPres : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ C / tyToFun {C} ∼ ] c₂) ≡ (c₁ ⟨ C / ∼ ⟩ c₂)
    tyToFunPres {C} ∼ c₁ c₂ = M-types.Rel.tyToFunPres (tyRel {C} ∼) c₁ c₂

    funToTyPres : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ ⟨ C / funToTy {C} ∼ ⟩ c₂) ≃ (c₁ [ C / ∼ ] c₂)
    funToTyPres ∼ c₁ c₂ = M-types.Rel.funToTyPres (funRel ∼) c₁ c₂
