{-# OPTIONS --without-K #-}

module M-types.equality where
    infix 4 _≡_
    data _≡_ {A : Set} (x : A) : A → Set where
        refl : x ≡ x
