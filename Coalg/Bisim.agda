{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Bisim (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim C =
        ∑[ coalg ∈ Coalg ]
        CoalgMor coalg C × CoalgMor coalg C

    coalg = pr₀

    tyRel : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] TyRel (ty C)
    tyRel (coalg , ρ₀ , ρ₁) = (ty coalg , fun ρ₀ , fun ρ₁)

    tyLift : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (c₀ ⟨ tyRel {C} ∼ ⟩ c₁ → (obs C c₀) ⟨ P-TyRel (tyRel {C} ∼) ⟩ (obs C c₁))
    tyLift ∼ c₀ c₁ (s , refl , refl) =
        (
            obs (coalg ∼) s ,
            ≡-apply (com (ρ₀ ∼)⁻¹) s ,
            ≡-apply (com (ρ₁ ∼)⁻¹) s
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
            P-CoalgMor {coalg ∼} {C} (ρ₀ ∼) ,
            P-CoalgMor {coalg ∼} {C} (ρ₁ ∼)
        )


    TyBisimMor : {C : Coalg} →
        TyBisim C → TyBisim C → Ty ℓ
    TyBisimMor {C} ∼ ≈ =
        ∑[ mor ∈ TyRelMor (tyRel {C} ∼) (tyRel {C} ≈) ]
        obs (coalg ≈) ∘ fun mor ≡ P-Fun (fun mor) ∘ obs (coalg ∼)


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim C =
        ∑[ funRel ∈ (ty C → ty C → Ty ℓ) ]
        ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (funRel c₀ c₁ → (P-FunRel funRel) (obs C c₀) (obs C c₁))

    funRel : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] FunRel (ty C)
    funRel = pr₀

    funLift : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (c₀ [ funRel ∼ ] c₁ → (obs C c₀) [ P-FunRel (funRel ∼) ] (obs C c₁))
    funLift = pr₁

    ≡-Bisim : {C : Coalg} →
        ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (≡-FunRel c₀ c₁ → P-FunRel ≡-FunRel (obs C c₀) (obs C c₁))
    ≡-Bisim c c refl = (refl , λ b → refl)

    ≡-FunBisim : {C : Coalg} →
        FunBisim C
    ≡-FunBisim {C} = (≡-FunRel , ≡-Bisim)

    P-FunBisim : {C : Coalg} →
        FunBisim C → FunBisim (P-Coalg C)
    P-FunBisim {C} ∼ =
        (
            P-FunRel (funRel ∼) ,
            λ (a , d₀) → λ (a , d₁) → λ (p , e) → (
                p ,
                λ b → pr₁ ∼ (d₀ b) (d₁ (tra B p b)) (e b)
            )
        )


    FunBisimMor : {C : Coalg} →
        FunBisim C → FunBisim C → Ty ℓ
    FunBisimMor {C} ∼ ≈ =
        ∑[ mor ∈ FunRelMor (funRel ∼) (funRel ≈) ]
        ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        funLift ≈ c₀ c₁ ∘ mor c₀ c₁ ≡
        P-FunRelMor mor (obs C c₀) (obs C c₁) ∘ funLift ∼ c₀ c₁


    TyBisim→FunBisim : {C : Coalg} →
        TyBisim C → FunBisim C
    TyBisim→FunBisim {C} ∼ =
        (
            (λ c₀ → λ c₁ → c₀ ⟨ tyRel {C} ∼ ⟩ c₁) ,
            (λ c₀ → λ c₁ → λ {(s , refl , refl) → let
                    q₀ :
                        obs C c₀ ≡ (
                            pr₀ (obs (coalg ∼) s) ,
                            fun (ρ₀ ∼) ∘ pr₁ (obs (coalg ∼) s)
                        )
                    q₀ = ≡-apply (com (ρ₀ ∼)) s

                    q₁ :
                        obs C c₁ ≡ (
                            pr₀ (obs (coalg ∼) s) ,
                            fun (ρ₁ ∼) ∘ pr₁ (obs (coalg ∼) s)
                        )
                    q₁ = ≡-apply (com (ρ₁ ∼)) s
                in (
                     (ap pr₀ q₀) · (ap pr₀ q₁)⁻¹ ,
                     λ b₀ → (
                         pr₁ (obs (coalg ∼) s) (tra B (ap pr₀ q₀) b₀) ,
                         (apply-pr₁ {C} q₀ b₀)⁻¹ ,
                         (apply-pr₁ {C} (q₁ ⁻¹) (tra B (ap pr₀ q₀) b₀)) ·
                         ap (pr₁ (obs C c₁)) (≡-apply (
                             tra-con B (ap pr₀ q₀) (ap pr₀ (q₁ ⁻¹)) ·
                             (ap (λ r → tra B (ap pr₀ q₀ · r)) ((ap-inv pr₀ q₁)⁻¹))
                         ) b₀)
                     )
                )
            })
        )

    FunBisim→TyBisim : {C : Coalg} →
        FunBisim C → TyBisim C
    FunBisim→TyBisim {C} ∼ =
        (
            (
                (∑[ c₀ ∈ ty C ] ∑[ c₁ ∈ ty C ] c₀ [ funRel ∼ ] c₁) ,
                (λ (c₀ , c₁ , s) → (
                    pr₀ (obs C c₀) ,
                    λ b₀ → (
                        pr₁ (obs C c₀) b₀ ,
                        pr₁ (obs C c₁) (tra B (pr₀ (funLift ∼ c₀ c₁ s)) b₀) ,
                        pr₁ (funLift ∼ c₀ c₁ s) b₀
                    )
                ))
            ) ,
            (
                pr₀ ,
                funext (λ (c₀ , c₁ , s) → ≡-pair (
                    refl ,
                    refl
                ))
            ) ,
            (
                pr₀ ∘ pr₁ ,
                funext (λ (c₀ , c₁ , s) → ≡-pair (
                    (pr₀ (funLift ∼ c₀ c₁ s)) ,
                    fun-tra (pr₀ (funLift ∼ c₀ c₁ s)) (pr₁ (obs C c₁))
                )⁻¹)
            )
        )


    TyBisim→FunBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ TyBisim C ] ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (c₀ [ funRel {C} (TyBisim→FunBisim {C} ∼) ] c₁) ≡ (c₀ ⟨ tyRel {C} ∼ ⟩ c₁)
    TyBisim→FunBisim-pres {C} ∼ c₀ c₁ = TyRel→FunRel-pres (tyRel {C} ∼) c₀ c₁

    FunBisim→TyBisim-pres : {C : Coalg} →
        ∏[ ∼ ∈ FunBisim C ] ∏[ c₀ ∈ ty C ] ∏[ c₁ ∈ ty C ]
        (c₀ ⟨ tyRel {C} (FunBisim→TyBisim {C} ∼) ⟩ c₁) ≃ (c₀ [ funRel {C} ∼ ] c₁)
    FunBisim→TyBisim-pres ∼ c₀ c₁ = FunRel→TyRel-pres (funRel ∼) c₀ c₁


    TyBisimMor→FunBisimMor : {C : Coalg} {∼ ≈ : TyBisim C} →
        TyBisimMor {C} ∼ ≈ → FunBisimMor {C} (TyBisim→FunBisim {C} ∼) (TyBisim→FunBisim {C} ≈)
    TyBisimMor→FunBisimMor {C} {∼} {≈} ((fun , refl , refl) , com) =
        (
            TyRelMor→FunRelMor (fun , refl , refl) ,
            λ c₀ → λ c₁ → funext (λ {(s , refl , refl) → {! ≡-apply com s  !}})
        )

    FunBisimMor→TyBisimMor : {C : Coalg} {∼ ≈ : FunBisim C} →
        FunBisimMor {C} ∼ ≈ → TyBisimMor {C} (FunBisim→TyBisim {C} ∼) (FunBisim→TyBisim {C} ≈)
    FunBisimMor→TyBisimMor {C} {∼} {≈} (mor , equ) =
        (
            FunRelMor→TyRelMor mor ,
            funext (λ (c₀ , c₁ , s) → {! ≡-apply (equ c₀ c₁) s  !})
        )
