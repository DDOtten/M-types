{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Core (A : Ty ℓ) (B : A → Ty ℓ) where
    P-Ty : Ty ℓ → Ty ℓ
    P-Ty X = ∑[ a ∈ A ] (B a → X)

    P-Fun : {X Y : Ty ℓ} →
        (X → Y) → (P-Ty X → P-Ty Y)
    P-Fun f = λ (a , d) → (a , f ∘ d)


    P-TyRel : {X : Ty ℓ} →
        TyRel X → TyRel (P-Ty X)
    P-TyRel {X} ∼ = (P-Ty (ty ∼) , P-Fun (ρ₁ ∼) , P-Fun (ρ₂ ∼))

    P-TyMor : {X : Ty ℓ} {∼ ≈ : TyRel X} →
        TyMor ∼ ≈ → TyMor (P-TyRel ∼) (P-TyRel ≈)
    P-TyMor {X} {∼} {≈} (f , inc₁ , inc₂) =
        (
            P-Fun f ,
            ap P-Fun inc₁ ,
            ap P-Fun inc₂
        )


    P-FunRel : {X : Ty ℓ} →
        FunRel X → FunRel (P-Ty X)
    P-FunRel {X} ∼ = λ (a₁ , d₁) → λ (a₂ , d₂) →
        ∑[ p ∈ a₁ ≡ a₂ ] ∏[ b₁ ∈ B a₁ ]
        (∼ (d₁ b₁) (d₂ (tra B p b₁)))

    P-FunMor : {X : Ty ℓ} {∼ ≈ : FunRel X} →
        FunMor ∼ ≈ → FunMor (P-FunRel ∼) (P-FunRel ≈)
    P-FunMor {X} {∼} {≈} f = λ (a₁ , d₁) → λ (a₂ , d₂) → λ (p , e) → (
            p ,
            λ b → f (d₁ b) (d₂ (tra B p b)) (e b)
        )


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P-Ty ty)

    obs : ∏[ C ∈ Coalg ] (ty C → P-Ty (ty C))
    obs (_ , obs) = obs

    P-coalg : Coalg → Coalg
    P-coalg C = (P-Ty (ty C) , P-Fun (obs C))


    Mor :  Coalg → Coalg → Ty ℓ
    Mor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        obs D ∘ fun ≡ P-Fun fun ∘ obs C

    com : {C D : Coalg} →
        ∏[ f ∈ (Mor C D) ]
        obs D ∘ fun f ≡ P-Fun (fun f) ∘ obs C
    com (_ , com) = com

    P-mor : {C D : Coalg} →
        Mor C D → Mor (P-coalg C) (P-coalg D)
    P-mor {C} {D} f =
        (
            P-Fun (fun f) ,
            ap P-Fun (com {C} {D} f)
        )
