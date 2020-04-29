{-# OPTIONS --without-K #-}

open import M-types.core

module M-types.coalg (A : Ty) (B : A → Ty) where
    open import M-types.equality
    open import M-types.sum
    open import M-types.product


    P : Ty → Ty
    P X = ∑[ a ∈ A ] (B a → X)

    Pfun : {X Y : Ty} → (X → Y) → (P X → P Y)
    Pfun f x' = (pr₁ x' , f ∘ pr₂ x')


    Coalg : Ty₁
    Coalg = ∑[ ty ∈ Ty ] (ty → P ty)

    ty : ∏[ C ∈ Coalg ] Ty
    ty (ty , obs) = ty

    obs : ∏[ C ∈ Coalg ] (ty C → P (ty C))
    obs (ty , obs) = obs


    Mor : (C D : Coalg) → Ty
    Mor C D =
        ∑[ fun ∈ (ty C → ty D) ]
        ∏[ c ∈ ty C ]
        (obs D (fun c) ≡ Pfun fun (obs C c))

    fun : {C D : Coalg} → ∏[ f ∈ (Mor C D) ]
        (ty C → ty D)
    fun (fun , com) = fun

    com : {C D : Coalg} → ∏[ f ∈ (Mor C D) ]
        ∏[ c ∈ ty C ]
        obs D (fun {C} {D} f c) ≡ Pfun {ty C} {ty D} (fun {C} {D} f) (obs C c)
    com (fun , com) = com
