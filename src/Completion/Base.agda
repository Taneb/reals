{-# OPTIONS --safe --without-K --guardedness #-}

open import Function.Metric.Rational.Core
open import Function.Metric.Rational.Structures
open import Relation.Binary

module Completion.Base {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {d : DistanceFunction A} (isMetric : IsMetric _≈_ d) where

open import Data.Product
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Rational.Base
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

open import Completion.Core d
import NatExtras as ℕ
open import RationalExtras
open import Stream

record Cauchy : Set a where
  field
    sequence : Stream A
    cauchy   : IsCauchy sequence

_≋_ : Rel Cauchy _
x ≋ y = ∀ ε → Positive ε → ∃[ N ] ∀ n → d (Cauchy.sequence x ! (N ℕ.+ n)) (Cauchy.sequence y ! (N ℕ.+ n)) < ε

≋-refl : Reflexive _≋_
≋-refl {x} ε ε-positive = 0 , λ n → begin-strict
  d (Cauchy.sequence x ! (0 ℕ.+ n)) (Cauchy.sequence x ! (0 ℕ.+ n)) ≡⟨ IsMetric.≈⇒0 isMetric (IsMetric.EqC.refl isMetric) ⟩
  0ℚ                                                                <⟨ positive⁻¹ ε-positive ⟩
  ε                                                                 ∎
  where open ≤-Reasoning

≋-sym : Symmetric _≋_
≋-sym {x} {y} x≋y ε ε-positive = N , λ n → begin-strict
  d (Cauchy.sequence y ! (N ℕ.+ n)) (Cauchy.sequence x ! (N ℕ.+ n)) ≡⟨ IsMetric.sym isMetric (Cauchy.sequence y ! (N ℕ.+ n)) (Cauchy.sequence x ! (N ℕ.+ n)) ⟩
  d (Cauchy.sequence x ! (N ℕ.+ n)) (Cauchy.sequence y ! (N ℕ.+ n)) <⟨ p n ⟩
  ε                                                                 ∎
  where
    N = proj₁ (x≋y ε ε-positive)
    p = proj₂ (x≋y ε ε-positive)
    open ≤-Reasoning

≋-trans : Transitive _≋_
≋-trans {x} {y} {z} x≋y y≋z ε ε-positive = M ℕ.⊔ N , λ n → begin-strict
  d (Cauchy.sequence x ! (M ℕ.⊔ N ℕ.+ n)) (Cauchy.sequence z ! (M ℕ.⊔ N ℕ.+ n))
    ≤⟨ IsMetric.triangle isMetric _ _ _ ⟩
  d (Cauchy.sequence x ! (M ℕ.⊔ N ℕ.+ n)) (Cauchy.sequence y ! (M ℕ.⊔ N ℕ.+ n)) + d (Cauchy.sequence y ! (M ℕ.⊔ N ℕ.+ n)) (Cauchy.sequence z ! (M ℕ.⊔ N ℕ.+ n))
    ≡⟨ cong₂ (λ j k → d (Cauchy.sequence x ! (j ℕ.+ n)) (Cauchy.sequence y ! (j ℕ.+ n)) + d (Cauchy.sequence y ! (k ℕ.+ n)) (Cauchy.sequence z ! (k ℕ.+ n))) (ℕ.m⊔n≡m+n∸m M N) (ℕ.m⊔n≡n+m∸n M N) ⟩
  d (Cauchy.sequence x ! ((M ℕ.+ (N ℕ.∸ M)) ℕ.+ n)) (Cauchy.sequence y ! ((M ℕ.+ (N ℕ.∸ M)) ℕ.+ n)) + d (Cauchy.sequence y ! ((N ℕ.+ (M ℕ.∸ N)) ℕ.+ n)) (Cauchy.sequence z ! ((N ℕ.+ (M ℕ.∸ N)) ℕ.+ n))
    ≡⟨ cong₂ (λ j k → d (Cauchy.sequence x ! j) (Cauchy.sequence y ! j) + d(Cauchy.sequence y ! k) (Cauchy.sequence z ! k)) (ℕ.+-assoc M (N ℕ.∸ M) n) (ℕ.+-assoc N (M ℕ.∸ N) n) ⟩
  d (Cauchy.sequence x ! (M ℕ.+ (N ℕ.∸ M ℕ.+ n))) (Cauchy.sequence y ! (M ℕ.+ (N ℕ.∸ M ℕ.+ n))) + d (Cauchy.sequence y ! (N ℕ.+ (M ℕ.∸ N ℕ.+ n))) (Cauchy.sequence z ! (N ℕ.+ (M ℕ.∸ N ℕ.+ n)))
    <⟨ +-mono-< (p (N ℕ.∸ M ℕ.+ n)) (q (M ℕ.∸ N ℕ.+ n)) ⟩
  ½ * ε + ½ * ε
    ≡˘⟨ *-distribʳ-+ ε ½ ½ ⟩
  1ℚ * ε
    ≡⟨ *-identityˡ ε ⟩
  ε
    ∎
  where
    M = proj₁ (x≋y (½ * ε) (pos*pos ½ ε _ ε-positive))
    p = proj₂ (x≋y (½ * ε) (pos*pos ½ ε _ ε-positive))
    N = proj₁ (y≋z (½ * ε) (pos*pos ½ ε _ ε-positive))
    q = proj₂ (y≋z (½ * ε) (pos*pos ½ ε _ ε-positive))
    open ≤-Reasoning

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl  = λ {x}     → ≋-refl  {x}
  ; sym   = λ {x y}   → ≋-sym   {x} {y}
  ; trans = λ {x y z} → ≋-trans {x} {y} {z}
  }
