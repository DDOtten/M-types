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
        ∏[ ∼ ∈ TyBisim C ] TyRel (ty C)
    tyRel (coalg , ρ₁ , ρ₂) = (ty coalg , fun ρ₁ , fun ρ₂)

    tyLift : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ ⟨ tyRel {C} ∼ ⟩ c₂ → (obs C c₁) ⟨ P-TyRel (tyRel {C} ∼) ⟩ (obs C c₂))
    tyLift ∼ c₁ c₂ (s , refl , refl) =
        (
            obs (coalg ∼) s ,
            ≡-apply (com (ρ₁ ∼)⁻¹) s ,
            ≡-apply (com (ρ₂ ∼)⁻¹) s
        )

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
        ∑[ mor ∈ TyRelMor (tyRel {C} ∼) (tyRel {C} ≈) ]
        obs (coalg ≈) ∘ fun mor ≡ P-Fun (fun mor) ∘ obs (coalg ∼)


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ funRel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (funRel c₁ c₂ → (P-FunRel funRel) (obs C c₁) (obs C c₂))

    funRel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] FunRel (ty C)
    funRel = pr₁

    funLift : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ funRel ∼ ] c₂ → (obs C c₁) [ P-FunRel (funRel ∼) ] (obs C c₂))
    funLift = pr₂

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


    FunBisimMor : {C : Coalg} →
        FunBisim C → FunBisim C → Ty ℓ
    FunBisimMor {C} ∼ ≈ =
        ∑[ mor ∈ FunRelMor (funRel ∼) (funRel ≈) ]
        ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        funLift ≈ c₁ c₂ ∘ mor c₁ c₂ ≡
        P-FunRelMor mor (obs C c₁) (obs C c₂) ∘ funLift ∼ c₁ c₂


    TyBisim→FunBisim : {C : Coalg} →
        TyBisim C → FunBisim C
    TyBisim→FunBisim {C} ∼ =
        (
            (λ c₁ → λ c₂ → c₁ ⟨ tyRel {C} ∼ ⟩ c₂) ,
            (λ c₁ → λ c₂ → λ {(s , refl , refl) → let
                    q₁ :
                        obs C c₁ ≡ (
                            pr₁ (obs (coalg ∼) s) ,
                            fun (ρ₁ ∼) ∘ pr₂ (obs (coalg ∼) s)
                        )
                    q₁ = ≡-apply (com (ρ₁ ∼)) s

                    q₂ :
                        obs C c₂ ≡ (
                            pr₁ (obs (coalg ∼) s) ,
                            fun (ρ₂ ∼) ∘ pr₂ (obs (coalg ∼) s)
                        )
                    q₂ = ≡-apply (com (ρ₂ ∼)) s
                in (
                     (ap pr₁ q₁) · (ap pr₁ q₂)⁻¹ ,
                     λ b₁ → (
                         pr₂ (obs (coalg ∼) s) (tra B (ap pr₁ q₁) b₁) ,
                         (apply-pr₂ {C} q₁ b₁)⁻¹ ,
                         (apply-pr₂ {C} (q₂ ⁻¹) (tra B (ap pr₁ q₁) b₁)) ·
                         ap (pr₂ (obs C c₂)) (≡-apply (
                             tra-con B (ap pr₁ q₁) (ap pr₁ (q₂ ⁻¹)) ·
                             (ap (λ r → tra B (ap pr₁ q₁ · r)) ((ap-inv pr₁ q₂)⁻¹))
                         ) b₁)
                     )
                )
            })
        )

    FunBisim→TyBisim : {C : Coalg} →
        FunBisim C → TyBisim C
    FunBisim→TyBisim {C} ∼ =
        (
            (
                (∑[ c₁ ∈ ty C ] ∑[ c₂ ∈ ty C ] c₁ [ funRel ∼ ] c₂) ,
                (λ (c₁ , c₂ , s) → (
                    pr₁ (obs C c₁) ,
                    λ b₁ → (
                        pr₂ (obs C c₁) b₁ ,
                        pr₂ (obs C c₂) (tra B (pr₁ (funLift ∼ c₁ c₂ s)) b₁) ,
                        pr₂ (funLift ∼ c₁ c₂ s) b₁
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
                pr₁ ∘ pr₂ ,
                funext (λ (c₁ , c₂ , s) → ≡-pair (
                    (pr₁ (funLift ∼ c₁ c₂ s)) ,
                    fun-tra (pr₁ (funLift ∼ c₁ c₂ s)) (pr₂ (obs C c₂))
                )⁻¹)
            )
        )


    TyBisim→FunBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ [ funRel {C} (TyBisim→FunBisim {C} ∼) ] c₂) ≡ (c₁ ⟨ tyRel {C} ∼ ⟩ c₂)
    TyBisim→FunBisim-pres {C} ∼ c₁ c₂ = TyRel→FunRel-pres (tyRel {C} ∼) c₁ c₂

    FunBisim→TyBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₁ ∈ ty C ] ∏[ c₂ ∈ ty C ]
        (c₁ ⟨ tyRel {C} (FunBisim→TyBisim {C} ∼) ⟩ c₂) ≃ (c₁ [ funRel {C} ∼ ] c₂)
    FunBisim→TyBisim-pres ∼ c₁ c₂ = FunRel→TyRel-pres (funRel ∼) c₁ c₂


    TyBisimMor→FunBisimMor : {C : Coalg} {∼ ≈ : TyBisim C} →
        TyBisimMor {C} ∼ ≈ → FunBisimMor (TyBisim→FunBisim {C} ∼) (TyBisim→FunBisim {C} ≈)
    TyBisimMor→FunBisimMor {C} {∼} {≈} ((fun , refl , refl) , com) =
        (
            TyRelMor→FunRelMor (fun , refl , refl) ,
            λ c₁ → λ c₂ → funext (λ {(s , refl , refl) → {! ≡-apply com s  !}})
        )
