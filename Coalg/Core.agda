{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Core (A : Ty ℓ) (B : A → Ty ℓ) where
    P-ty : Ty ℓ → Ty ℓ
    P-ty X = ∑[ a ∈ A ] (B a → X)

    P-fun : {X Y : Ty ℓ} →
        (X → Y) → (P-ty X → P-ty Y)
    P-fun f = λ (a , d) → (a , f ∘ d)

    P-tyRel : {X : Ty ℓ} →
        TyRel X → TyRel (P-ty X)
    P-tyRel {X} ∼ = (P-ty (ty ∼) , P-fun (ρ₁ ∼) , P-fun (ρ₂ ∼))

    P-funRel : {X : Ty ℓ} →
        FunRel X → FunRel (P-ty X)
    P-funRel {X} ∼ = λ (a₁ , d₁) → λ (a₂ , d₂) →
        ∑[ p ∈ a₁ ≡ a₂ ] ∏[ b₁ ∈ B a₁ ]
        (∼ (d₁ b₁) (d₂ (tra B p b₁)))


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P-ty ty)

    obs : ∏[ C ∈ Coalg ] (ty C → P-ty (ty C))
    obs (_ , obs) = obs

    P-coalg : Coalg → Coalg
    P-coalg C = (P-ty (ty C) , P-fun (obs C))


    Mor : (C D : Coalg) → Ty ℓ
    Mor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        ∏[ c ∈ ty C ] obs D (fun c) ≡ P-fun fun (obs C c)

    com : {C D : Coalg} →
        ∏[ f ∈ (Mor C D) ]
        ∏[ c ∈ ty C ] obs D (fun f c) ≡ P-fun (fun f) (obs C c)
    com (_ , com) = com

    P-mor : {C D : Coalg} →
        Mor C D → Mor (P-coalg C) (P-coalg D)
    P-mor {C} {D} f =
        (
            P-fun (fun f) ,
            ≡-apply (ap P-fun (funext (com {C} {D} f)))
        )
