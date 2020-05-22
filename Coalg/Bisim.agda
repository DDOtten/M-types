{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Bisim (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        CoalgMor coalg C × CoalgMor coalg C

    coalg = pr₁

    tyRel : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] M-types.Rel.TyRel (ty C)
    tyRel (coalg , ρ₁ , ρ₂) = (ty coalg , fun ρ₁ , fun ρ₂)

    TyBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    TyBisim-syntax C ∼ c₁ c₂ = TyRel-syntax (tyRel {C} ∼) c₁ c₂
    syntax TyBisim-syntax C ∼ c₁ c₂ = c₁ ⟨ C / ∼ ⟩ c₂

    ≡-TyBisim : {C : Coalg} →
        TyBisim C
    ≡-TyBisim {C} =
        (
            C ,
            (id , refl) ,
            (id , refl)
        )

    P-TyBisim : {C : Coalg} →
        TyBisim C → TyBisim (P-Coalg C)
    P-TyBisim {C} ∼ =
        (
            P-Coalg (coalg ∼) ,
            P-CoalgMor {coalg ∼} {C} (ρ₁ ∼) ,
            P-CoalgMor {coalg ∼} {C} (ρ₂ ∼)
        )


    TyBisimMor : {C : Coalg} →
        TyBisim C → TyBisim C → Ty ℓ
    TyBisimMor {C} ∼ ≈ =
        ∑[ mor ∈ CoalgMor (coalg ∼) (coalg ≈) ]
        (∘-CoalgMor {coalg ∼} {coalg ≈} {C} (ρ₁ ≈) mor ≡ (ρ₁ ∼)) ×
        (∘-CoalgMor {coalg ∼} {coalg ≈} {C} (ρ₂ ≈) mor ≡ (ρ₂ ∼))


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ funRel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (funRel c₁ c₂ → (P-FunRel funRel) (obs C c₁) (obs C c₂))

    funRel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] M-types.Rel.FunRel (ty C)
    funRel (funRel , _) = funRel

    FunBisim-syntax :
        ∏[ C ∈ Coalg ] ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ] Ty ℓ
    FunBisim-syntax C ∼ c₁ c₂ = FunRel-syntax (funRel ∼) c₁ c₂
    syntax FunBisim-syntax C ∼ c₁ c₂ = c₁ [ C / ∼ ] c₂

    ≡-Bisim : {C : Coalg} →
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (≡-FunRel c₁ c₂ → P-FunRel ≡-FunRel (obs C c₁) (obs C c₂))
    ≡-Bisim c c refl = (refl , λ b → refl)

    ≡-FunBisim : {C : Coalg} →
        FunBisim C
    ≡-FunBisim {C} = (≡-FunRel , ≡-Bisim)

    P-FunBisim : {C : Coalg} →
        FunBisim C → FunBisim (P-Coalg C)
    P-FunBisim {C} ∼ =
        (
            P-FunRel (funRel ∼) ,
            λ (a , d₁) → λ (a , d₂) → λ (p , e) → (
                p ,
                λ b → pr₂ ∼ (d₁ b) (d₂ (tra B p b)) (e b)
            )
        )

    funBisim = pr₂


    FunBisimMor : {C : Coalg} →
        FunBisim C → FunBisim C → Ty ℓ
    FunBisimMor {C} ∼ ≈ =
        ∑[ mor ∈ FunRelMor (ty ∼) (ty ≈) ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        funBisim ≈ c₁ c₂ ∘ mor c₁ c₂ ≡
        P-FunRelMor mor (obs C c₁) (obs C c₂) ∘ funBisim ∼ c₁ c₂


    TyBisim→FunBisim : {C : Coalg} →
        TyBisim C → FunBisim C
    TyBisim→FunBisim {C} ∼ =
        (
            (λ c₁ → λ c₂ → c₁ ⟨ C / ∼ ⟩ c₂) ,
            (λ c₁ → λ c₂ → λ (s , p₁ , p₂) → let
                q₁ = begin
                        obs C c₁
                    ≡⟨ ap (obs C) (p₁ ⁻¹) ⟩
                        obs C (fun (ρ₁ ∼) s)
                    ≡⟨ ≡-apply (com (ρ₁ ∼)) s ⟩
                        (
                            pr₁ (obs (coalg ∼) s) ,
                            fun (ρ₁ ∼) ∘ pr₂ (obs (coalg ∼) s)
                        )
                    ∎
                q₂ = begin
                        obs C c₂
                    ≡⟨ ap (obs C) (p₂ ⁻¹) ⟩
                        obs C (fun (ρ₂ ∼) s)
                    ≡⟨ ≡-apply (com (ρ₂ ∼)) s ⟩
                        (
                            pr₁ (obs (coalg ∼) s) ,
                            fun (ρ₂ ∼) ∘ pr₂ (obs (coalg ∼) s)
                        )
                    ∎
            in (
                (ap pr₁ q₁) · (ap pr₁ q₂)⁻¹ ,
                (λ b₁ → (
                    pr₂ (obs (coalg ∼) s) (tra B (ap pr₁ q₁) b₁),
                    (apply-pr₂ q₁ b₁)⁻¹ ,
                    (apply-pr₂ (q₂ ⁻¹) (tra B (ap pr₁ q₁) b₁)) ·
                    ap (pr₂ (obs C c₂)) (≡-apply (
                        tra-con B (ap pr₁ q₁) (ap pr₁ (q₂ ⁻¹)) ·
                        (ap (λ r → tra B (ap pr₁ q₁ · r)) ((ap-inv pr₁ q₂)⁻¹))
                    ) b₁)
                ))
            ))
        ) where
            apply-pr₂ : {(a₁ , d₁) (a₂ , d₂) : P (ty C)} →
                ∏[ p ∈ (a₁ , d₁) ≡ (a₂ , d₂) ] ∏[ b₁ ∈ B a₁ ]
                d₁ b₁ ≡ d₂ (tra B (ap pr₁ p) b₁)
            apply-pr₂ refl b = refl

    FunBisim→TyBisim : {C : Coalg} →
        FunBisim C → TyBisim C
    FunBisim→TyBisim {C} ∼ =
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


    TyBisim→FunBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ C / TyBisim→FunBisim {C} ∼ ] c₂) ≡ (c₁ ⟨ C / ∼ ⟩ c₂)
    TyBisim→FunBisim-pres {C} ∼ c₁ c₂ = TyRel→FunRel-pres (tyRel {C} ∼) c₁ c₂

    FunBisim→TyBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ ⟨ C / FunBisim→TyBisim {C} ∼ ⟩ c₂) ≃ (c₁ [ C / ∼ ] c₂)
    FunBisim→TyBisim-pres ∼ c₁ c₂ = FunRel→TyRel-pres (funRel ∼) c₁ c₂
