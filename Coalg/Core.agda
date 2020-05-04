{-# OPTIONS --without-K #-}


open import M-types.Base
open import M-types.Rel


module M-types.Coalg.Core {ℓ : Level} (A : Ty ℓ) (B : A → Ty ℓ) where
    P : Ty ℓ → Ty ℓ
    P X = ∑[ a ∈ A ] (B a → X)

    Pfun : {X Y : Ty ℓ} →
        (X → Y) → (P X → P Y)
    Pfun f px = (pr₁ px , f ∘ pr₂ px )

    Pbar : {X : Ty ℓ} →
        FunRel X → FunRel (P X)
    Pbar {X} ∼ px₁ px₂ =
        ∑[ p ∈ pr₁ px₁ ≡ pr₁ px₂ ]
        ∏[ b₁ ∈ B (pr₁ px₁) ]
        (∼ (pr₂ px₁ b₁) (pr₂ px₂ (tra B p b₁)))


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P ty)

    obs : ∏[ C ∈ Coalg ] (ty C → P (ty C))
    obs (ty , obs) = obs


    Mor : (C D : Coalg) → Ty ℓ
    Mor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        ∏[ c ∈ ty C ]
        (obs D (fun c) ≡ Pfun fun (obs C c))

    com : {C D : Coalg} →
        ∏[ f ∈ (Mor C D) ]
        ∏[ c ∈ ty C ]
        obs D (fun f c) ≡ Pfun (fun f) (obs C c)
    com (fun , com) = com
