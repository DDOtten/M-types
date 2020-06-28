{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.Bisim (A : Ty ℓ) (B : A → Ty ℓ) where
    open import M-types.Coalg.Core A B


    TyBisim : Coalg → Ty (ℓ-suc ℓ)
    TyBisim X =
        ∑[ coalg ∈ Coalg ]
        CoalgMor coalg X × CoalgMor coalg X

    coalg = pr₀

    spanRel : {X : Coalg} →
        ∏[ ∼ ∈ TyBisim X ] SpanRel (ty X)
    spanRel (coalg , ρ₀ , ρ₁) = (ty coalg , fun ρ₀ , fun ρ₁)

    tyLift : {X : Coalg} →
        ∏[ ∼ ∈ TyBisim X ] ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        (x₀ ⟨ spanRel {X} ∼ ⟩ x₁ → (obs X x₀) ⟨ P-SpanRel (spanRel {X} ∼) ⟩ (obs X x₁))
    tyLift ∼ x₀ x₁ (s , refl , refl) =
        (
            obs (coalg ∼) s ,
            ≡-apply (com (ρ₀ ∼)⁻¹) s ,
            ≡-apply (com (ρ₁ ∼)⁻¹) s
        )

    ≡-TyBisim : {X : Coalg} →
        TyBisim X
    ≡-TyBisim {X} =
        (
            X ,
            (id , refl) ,
            (id , refl)
        )

    P-TyBisim : {X : Coalg} →
        TyBisim X → TyBisim (P-Coalg X)
    P-TyBisim {X} ∼ =
        (
            P-Coalg (coalg ∼) ,
            P-CoalgMor {coalg ∼} {X} (ρ₀ ∼) ,
            P-CoalgMor {coalg ∼} {X} (ρ₁ ∼)
        )


    TyBisimMor : {X : Coalg} →
        TyBisim X → TyBisim X → Ty ℓ
    TyBisimMor {X} ∼ ≈ =
        ∑[ mor ∈ SpanRelMor (spanRel {X} ∼) (spanRel {X} ≈) ]
        obs (coalg ≈) ∘ fun mor ≡ P-Fun (fun mor) ∘ obs (coalg ∼)


    FunBisim : Coalg → Ty (ℓ-suc ℓ)
    FunBisim X =
        ∑[ depRel ∈ (ty X → ty X → Ty ℓ) ]
        ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        (depRel x₀ x₁ → (P-DepRel depRel) (obs X x₀) (obs X x₁))

    depRel : {X : Coalg} →
        ∏[ ∼ ∈ FunBisim X ] DepRel (ty X)
    depRel = pr₀

    funLift : {X : Coalg} →
        ∏[ ∼ ∈ FunBisim X ] ∏[ d₀ ∈ ty X ] ∏[ d₁ ∈ ty X ]
        (d₀ [ depRel ∼ ] d₁ → (obs X d₀) [ P-DepRel (depRel ∼) ] (obs X d₁))
    funLift = pr₁

    ≡-funLift : {X : Coalg} →
        ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        (≡-depRel x₀ x₁ → P-DepRel ≡-depRel (obs X x₀) (obs X x₁))
    ≡-funLift x x refl = (refl , λ b → refl)

    ≡-funBisim : {X : Coalg} →
        FunBisim X
    ≡-funBisim {X} = (≡-depRel , ≡-funLift)

    P-FunBisim : {X : Coalg} →
        FunBisim X → FunBisim (P-Coalg X)
    P-FunBisim {X} ∼ =
        (
            P-DepRel (depRel ∼) ,
            λ (a₀ , d₀) → λ (a₁ , d₁) → λ (p , e) → (
                p ,
                λ b₀ → pr₁ ∼ (d₀ b₀) (d₁ (tra B p b₀)) (e b₀)
            )
        )


    FunBisimMor : {X : Coalg} →
        FunBisim X → FunBisim X → Ty ℓ
    FunBisimMor {X} ∼ ≈ =
        ∑[ mor ∈ DepRelMor (depRel ∼) (depRel ≈) ]
        ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        funLift ≈ x₀ x₁ ∘ mor x₀ x₁ ≡
        P-DepRelMor mor (obs X x₀) (obs X x₁) ∘ funLift ∼ x₀ x₁


    fun-tra : {a₀ a₁ : A} {C : Ty ℓ} →
        ∏[ p ∈ a₀ ≡ a₁ ] ∏[ f₁ ∈ (B a₁ → C) ]
        tra (λ a → (B a → C)) p (f₁ ∘ (tra B p)) ≡ f₁
    fun-tra refl f₁ = refl

    apply-pr₁ : {X : Coalg} {(a₀ , d₀) (a₁ , d₁) : P (ty X)} →
        ∏[ p ∈ (a₀ , d₀) ≡ (a₁ , d₁) ] ∏[ b₀ ∈ B a₀ ]
        d₀ b₀ ≡ d₁ (tra B (ap pr₀ p) b₀)
    apply-pr₁ refl b = refl


    TyBisim→FunBisim : {X : Coalg} →
        TyBisim X → FunBisim X
    TyBisim→FunBisim {X} ∼ =
        (
            (λ x₀ → λ x₁ → x₀ ⟨ spanRel {X} ∼ ⟩ x₁) ,
            (λ x₀ → λ x₁ → λ {(s , refl , refl) → let
                q₀ :
                    obs X x₀ ≡ (
                        pr₀ (obs (coalg ∼) s) ,
                        fun (ρ₀ ∼) ∘ pr₁ (obs (coalg ∼) s)
                    )
                q₀ = ≡-apply (com (ρ₀ ∼)) s

                q₁ :
                    obs X x₁ ≡ (
                        pr₀ (obs (coalg ∼) s) ,
                        fun (ρ₁ ∼) ∘ pr₁ (obs (coalg ∼) s)
                    )
                q₁ = ≡-apply (com (ρ₁ ∼)) s
            in (
                 (ap pr₀ q₀) · (ap pr₀ q₁) ⁻¹ ,
                 λ b₀ → (
                     pr₁ (obs (coalg ∼) s) (tra B (ap pr₀ q₀) b₀) ,
                     (apply-pr₁ {X} q₀ b₀) ⁻¹ ,
                     (apply-pr₁ {X} (q₁ ⁻¹) (tra B (ap pr₀ q₀) b₀)) ·
                     ap (pr₁ (obs X x₁)) (≡-apply (
                         tra-con B (ap pr₀ q₀) (ap pr₀ (q₁ ⁻¹)) ·
                         ap (λ r → tra B (ap pr₀ q₀ · r)) ((ap-inv pr₀ q₁) ⁻¹)
                     ) b₀)
                 )
            )})
        )

    FunBisim→TyBisim : {X : Coalg} →
        FunBisim X → TyBisim X
    FunBisim→TyBisim {X} ∼ =
        (
            (
                (∑[ x₀ ∈ ty X ] ∑[ x₁ ∈ ty X ] x₀ [ depRel ∼ ] x₁) ,
                λ (x₀ , x₁ , s) → (
                    pr₀ (obs X x₀) ,
                    λ b₀ → (
                        pr₁ (obs X x₀) b₀ ,
                        pr₁ (obs X x₁) (tra B (pr₀ (funLift ∼ x₀ x₁ s)) b₀) ,
                        pr₁ (funLift ∼ x₀ x₁ s) b₀
                    )
                )
            ) , (
                pr₀ ,
                funext (λ (x₀ , x₁ , s) → refl)
            ) , (
                pr₀ ∘ pr₁ ,
                funext (λ (x₀ , x₁ , s) → ≡-pair (
                    pr₀ (funLift ∼ x₀ x₁ s) ,
                    fun-tra (pr₀ (funLift ∼ x₀ x₁ s)) (pr₁ (obs X x₁))
                ) ⁻¹)
            )
        )


    TyBisim→FunBisim-pres : {X : Coalg} →
        ∏[ ∼ ∈ TyBisim X ] ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        (x₀ [ depRel {X} (TyBisim→FunBisim {X} ∼) ] x₁) ≡ (x₀ ⟨ spanRel {X} ∼ ⟩ x₁)
    TyBisim→FunBisim-pres {X} ∼ x₀ x₁ = SpanRel→DepRel-pres (spanRel {X} ∼) x₀ x₁

    FunBisim→TyBisim-pres : {X : Coalg} →
        ∏[ ∼ ∈ FunBisim X ] ∏[ x₀ ∈ ty X ] ∏[ x₁ ∈ ty X ]
        (x₀ ⟨ spanRel {X} (FunBisim→TyBisim {X} ∼) ⟩ x₁) ≃ (x₀ [ depRel {X} ∼ ] x₁)
    FunBisim→TyBisim-pres ∼ x₀ x₁ = DepRel→SpanRel-pres (depRel ∼) x₀ x₁
