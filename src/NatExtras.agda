{-# OPTIONS --safe --without-K #-}
module NatExtras where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- these should be in Data.Nat.Properties
m⊔n≡m+n∸m : ∀ m n → m ⊔ n ≡ m + (n ∸ m)
m⊔n≡m+n∸m zero n = refl
m⊔n≡m+n∸m (suc m) zero = sym (cong suc (+-identityʳ m))
m⊔n≡m+n∸m (suc m) (suc n) = cong suc (m⊔n≡m+n∸m m n)

m⊔n≡n+m∸n : ∀ m n → m ⊔ n ≡ n + (m ∸ n)
m⊔n≡n+m∸n zero n = sym (trans (cong (n +_) (0∸n≡0 n)) (+-identityʳ n))
m⊔n≡n+m∸n (suc m) zero = refl
m⊔n≡n+m∸n (suc m) (suc n) = cong suc (m⊔n≡n+m∸n m n)

