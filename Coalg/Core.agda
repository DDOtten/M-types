{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Core (A : Ty ℓ) (B : A → Ty ℓ) where
    P : Ty ℓ → Ty ℓ
    P X = ∑[ a ∈ A ] (B a → X)

    P-Fun : {X Y : Ty ℓ} →
        (X → Y) → (P X → P Y)
    P-Fun f = λ (a , d) → (a , f ∘ d)


    P-TyRel : {X : Ty ℓ} →
        TyRel X → TyRel (P X)
    P-TyRel {X} ∼ = (P (ty ∼) , P-Fun (ρ₁ ∼) , P-Fun (ρ₂ ∼))

    P-TyRelMor : {X : Ty ℓ} {∼ ≈ : TyRel X} →
        TyRelMor ∼ ≈ → TyRelMor (P-TyRel ∼) (P-TyRel ≈)
    P-TyRelMor {X} {∼} {≈} (fun , refl , refl) =
        (
            P-Fun fun ,
            refl ,
            refl
        )


    P-FunRel : {X : Ty ℓ} →
        FunRel X → FunRel (P X)
    P-FunRel {X} ∼ = λ (a₁ , d₁) → λ (a₂ , d₂) →
        ∑[ p ∈ a₁ ≡ a₂ ] ∏[ b₁ ∈ B a₁ ]
        d₁ b₁ [ ∼ ] d₂ (tra B p b₁)

    P-FunRelMor : {X : Ty ℓ} {∼ ≈ : FunRel X} →
        FunRelMor ∼ ≈ → FunRelMor (P-FunRel ∼) (P-FunRel ≈)
    P-FunRelMor {X} {∼} {≈} f = λ (a₁ , d₁) → λ (a₂ , d₂) → λ (p , e) → (
            p ,
            λ b → f (d₁ b) (d₂ (tra B p b)) (e b)
        )


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P ty)

    obs = pr₂

    P-Coalg : Coalg → Coalg
    P-Coalg C = (P (ty C) , P-Fun (obs C))


    CoalgMor :  Coalg → Coalg → Ty ℓ
    CoalgMor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        obs D ∘ fun ≡ P-Fun fun ∘ obs C

    com = pr₂

    P-CoalgMor : {C D : Coalg} →
        CoalgMor C D → CoalgMor (P-Coalg C) (P-Coalg D)
    P-CoalgMor {C} {D} f =
        (
            P-Fun (fun f) ,
            ap P-Fun (com f)
        )


    apply-pr₂ : {C : Coalg} {(a₁ , d₁) (a₂ , d₂) : P (ty C)} →
        ∏[ p ∈ (a₁ , d₁) ≡ (a₂ , d₂) ] ∏[ b₁ ∈ B a₁ ]
        d₁ b₁ ≡ d₂ (tra B (ap pr₁ p) b₁)
    apply-pr₂ refl b = refl

    fun-tra : {a₁ a₂ : A} {X : Ty ℓ} →
        ∏[ p ∈ a₁ ≡ a₂ ] ∏[ f₂ ∈ (B a₂ → X) ]
        tra (λ a → (B a → X)) p (f₂ ∘ (tra B p)) ≡ f₂
    fun-tra refl f₂ = refl
