{-# OPTIONS --without-K #-}


open import M-types.Base


module M-types.Coalg.Core (A : Ty ℓ) (B : A → Ty ℓ) where
    P : Ty ℓ → Ty ℓ
    P X = ∑[ a ∈ A ] (B a → X)

    P-Fun : {X Y : Ty ℓ} →
        (X → Y) → (P X → P Y)
    P-Fun f = λ (a , d) → (a , f ∘ d)


    P-SpanRel : {X : Ty ℓ} →
        SpanRel X → SpanRel (P X)
    P-SpanRel {X} ∼ = (P (ty ∼) , P-Fun (ρ₀ ∼) , P-Fun (ρ₁ ∼))

    P-SpanRelMor : {X : Ty ℓ} {∼ ≈ : SpanRel X} →
        SpanRelMor ∼ ≈ → SpanRelMor (P-SpanRel ∼) (P-SpanRel ≈)
    P-SpanRelMor {X} {∼} {≈} f =
        (
            P-Fun (fun f) ,
            ap P-Fun (com₀ f) ,
            ap P-Fun (com₁ f)
        )


    P-DepRel : {X : Ty ℓ} →
        DepRel X → DepRel (P X)
    P-DepRel {X} ∼ = λ (a₀ , d₀) → λ (a₁ , d₁) →
        ∑[ p ∈ a₀ ≡ a₁ ] ∏[ b₀ ∈ B a₀ ]
        d₀ b₀ [ ∼ ] d₁ (tra B p b₀)

    P-DepRelMor : {X : Ty ℓ} {∼ ≈ : DepRel X} →
        DepRelMor ∼ ≈ → DepRelMor (P-DepRel ∼) (P-DepRel ≈)
    P-DepRelMor {X} {∼} {≈} f = λ (a₀ , d₀) → λ (a₁ , d₁) → λ (p , e) → (
            p ,
            λ b₀ → f (d₀ b₀) (d₁ (tra B p b₀)) (e b₀)
        )


    Coalg : Ty (ℓ-suc ℓ)
    Coalg = ∑[ ty ∈ Ty ℓ ] (ty → P ty)

    obs = pr₁

    P-Coalg : Coalg → Coalg
    P-Coalg X = (P (ty X) , P-Fun (obs X))


    CoalgMor :  Coalg → Coalg → Ty ℓ
    CoalgMor X Y =
        ∑[ fun ∈ (ty X → ty Y) ]
        obs Y ∘ fun ≡ P-Fun fun ∘ obs X

    com = pr₁

    P-CoalgMor : {X Y : Coalg} →
        CoalgMor X Y → CoalgMor (P-Coalg X) (P-Coalg Y)
    P-CoalgMor {X} {Y} f =
        (
            P-Fun (fun f) ,
            ap P-Fun (com f)
        )
