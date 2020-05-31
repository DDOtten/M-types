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
    P-TyRel {X} ∼ = (P (ty ∼) , P-Fun (ρ₀ ∼) , P-Fun (ρ₁ ∼))

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
    P-FunRel {X} ∼ = λ (a₀ , d₀) → λ (a₁ , d₁) →
        ∑[ p ∈ a₀ ≡ a₁ ] ∏[ b₀ ∈ B a₀ ]
        d₀ b₀ [ ∼ ] d₁ (tra B p b₀)

    P-FunRelMor : {X : Ty ℓ} {∼ ≈ : FunRel X} →
        FunRelMor ∼ ≈ → FunRelMor (P-FunRel ∼) (P-FunRel ≈)
    P-FunRelMor {X} {∼} {≈} f = λ (a₀ , d₀) → λ (a₁ , d₁) → λ (p , e) → (
            p ,
            λ b → f (d₀ b) (d₁ (tra B p b)) (e b)
        )


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P ty)

    obs = pr₁

    P-Coalg : Coalg → Coalg
    P-Coalg C = (P (ty C) , P-Fun (obs C))


    CoalgMor :  Coalg → Coalg → Ty ℓ
    CoalgMor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        obs D ∘ fun ≡ P-Fun fun ∘ obs C

    com = pr₁

    P-CoalgMor : {C D : Coalg} →
        CoalgMor C D → CoalgMor (P-Coalg C) (P-Coalg D)
    P-CoalgMor {C} {D} f =
        (
            P-Fun (fun f) ,
            ap P-Fun (com f)
        )


    apply-pr₁ : {C : Coalg} {(a₀ , d₀) (a₁ , d₁) : P (ty C)} →
        ∏[ p ∈ (a₀ , d₀) ≡ (a₁ , d₁) ] ∏[ b₀ ∈ B a₀ ]
        d₀ b₀ ≡ d₁ (tra B (ap pr₀ p) b₀)
    apply-pr₁ refl b = refl

    fun-tra : {a₀ a₁ : A} {X : Ty ℓ} →
        ∏[ p ∈ a₀ ≡ a₁ ] ∏[ f₁ ∈ (B a₁ → X) ]
        tra (λ a → (B a → X)) p (f₁ ∘ (tra B p)) ≡ f₁
    fun-tra refl f₁ = refl
