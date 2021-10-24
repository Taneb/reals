{-# OPTIONS --safe --without-K --guardedness #-}
module Real where

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚ
open import Function.Metric.Rational
open import Function.Nary.NonDependent using (congₙ)
open import Relation.Binary.PropositionalEquality

open import RationalMetric
open import Completion.Core (λ x y → ℚ.∣ x ℚ.- y ∣)
import Completion.Base as Completion
import NatExtras as ℕ
import RationalExtras as ℚ
open import Stream

open Completion ∣x-y∣-isMetric public
  renaming (Cauchy to ℝ)

fromℚ : ℚ → ℝ
fromℚ x = record
  { sequence = repeat x
  ; cauchy   = λ ε ε-positive → 0 , λ m n → begin-strict
    ℚ.∣ repeat x ! m ℚ.- repeat x ! n ∣ ≡⟨ cong₂ (λ j k → ℚ.∣ j ℚ.- k ∣) (repeat-! x m) (repeat-! x n) ⟩
    ℚ.∣ x ℚ.- x ∣                       ≡⟨ cong ℚ.∣_∣ (ℚ.+-inverseʳ x) ⟩
    0ℚ                                  <⟨ ℚ.positive⁻¹ ε-positive ⟩
    ε                                   ∎
  }
  where open ℚ.≤-Reasoning

0ℝ : ℝ
0ℝ = fromℚ 0ℚ

1ℝ : ℝ
1ℝ = fromℚ 1ℚ

+-sequence : Stream ℚ → Stream ℚ → Stream ℚ
+-sequence = zipWith ℚ._+_

+-cauchy : ∀ {xs ys : Stream ℚ} (xs-cauchy : IsCauchy xs) (ys-cauchy : IsCauchy ys) → IsCauchy (+-sequence xs ys)
+-cauchy {xs} {ys} xs-cauchy ys-cauchy ε ε-positive = M ℕ.⊔ N , λ m n → begin-strict
  ℚ.∣ +-sequence xs ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.- +-sequence xs ys ! (M ℕ.⊔ N ℕ.+ n) ∣ ≡⟨ cong₂ (λ j k → ℚ.∣ j ℚ.- k ∣) (zipWith-! ℚ._+_ xs ys (M ℕ.⊔ N ℕ.+ m)) (zipWith-! ℚ._+_ xs ys (M ℕ.⊔ N ℕ.+ n)) ⟩
  ℚ.∣ (xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ ys ! (M ℕ.⊔ N ℕ.+ m)) ℚ.- (xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.+ ys ! (M ℕ.⊔ N ℕ.+ n)) ∣ ≡⟨ cong (λ k → ℚ.∣ (xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ ys ! (M ℕ.⊔ N ℕ.+ m)) ℚ.+ k ∣) (ℚ.neg-distrib-+ (xs ! (M ℕ.⊔ N ℕ.+ n)) (ys ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ (xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ ys ! (M ℕ.⊔ N ℕ.+ m)) ℚ.+ (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n)) ∣ ≡⟨ cong ℚ.∣_∣ (ℚ.+-assoc (xs ! (M ℕ.⊔ N ℕ.+ m)) (ys ! (M ℕ.⊔ N ℕ.+ m)) (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ (ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ∣ ≡˘⟨ cong (λ k → ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ k ∣) (ℚ.+-assoc (ys ! (M ℕ.⊔ N ℕ.+ m)) (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n)) (ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ ((ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n)) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n)) ∣ ≡⟨ cong (λ k → ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ (k ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n)) ∣) (ℚ.+-comm (ys ! (M ℕ.⊔ N ℕ.+ m)) (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ ((ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.+ ys ! (M ℕ.⊔ N ℕ.+ m)) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n)) ∣ ≡⟨ cong (λ k → ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ k ∣) (ℚ.+-assoc (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n)) (ys ! (M ℕ.⊔ N ℕ.+ m)) (ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.+ (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n) ℚ.+ (ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ∣ ≡˘⟨ cong ℚ.∣_∣ (ℚ.+-assoc (xs ! (M ℕ.⊔ N ℕ.+ m)) (ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n)) (ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n))) ⟩
  ℚ.∣ (xs ! (M ℕ.⊔ N ℕ.+ m) ℚ.- xs ! (M ℕ.⊔ N ℕ.+ n)) ℚ.+ (ys ! (M ℕ.⊔ N ℕ.+ m) ℚ.- ys ! (M ℕ.⊔ N ℕ.+ n)) ∣ ≡⟨ cong₂ (λ j k → ℚ.∣ (xs ! (j ℕ.+ m) ℚ.- xs ! (j ℕ.+ n)) ℚ.+ (ys ! (k ℕ.+ m) ℚ.- ys ! (k ℕ.+ n)) ∣) (ℕ.m⊔n≡m+n∸m M N) (ℕ.m⊔n≡n+m∸n M N) ⟩
  ℚ.∣ (xs ! ((M ℕ.+ (N ℕ.∸ M)) ℕ.+ m) ℚ.- xs ! ((M ℕ.+ (N ℕ.∸ M)) ℕ.+ n)) ℚ.+ (ys ! ((N ℕ.+ (M ℕ.∸ N)) ℕ.+ m) ℚ.- ys ! ((N ℕ.+ (M ℕ.∸ N)) ℕ.+ n)) ∣ ≡⟨ congₙ 4 (λ i j k l → ℚ.∣ (xs ! i ℚ.- xs ! j) ℚ.+ (ys ! k ℚ.- ys ! l) ∣) (ℕ.+-assoc M (N ℕ.∸ M) m) (ℕ.+-assoc M (N ℕ.∸ M) n) (ℕ.+-assoc N (M ℕ.∸ N) m) (ℕ.+-assoc N (M ℕ.∸ N) n)  ⟩
  ℚ.∣ (xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ m)) ℚ.- xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ n))) ℚ.+ (ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ m)) ℚ.- ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ n))) ∣ ≤⟨ ℚ.∣p+q∣≤∣p∣+∣q∣ (xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ m)) ℚ.- xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ n))) (ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ m)) ℚ.- ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ n))) ⟩
  ℚ.∣ xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ m)) ℚ.- xs ! (M ℕ.+ (N ℕ.∸ M ℕ.+ n)) ∣ ℚ.+ ℚ.∣ ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ m)) ℚ.- ys ! (N ℕ.+ (M ℕ.∸ N ℕ.+ n)) ∣ <⟨ ℚ.+-mono-< (p (N ℕ.∸ M ℕ.+ m) (N ℕ.∸ M ℕ.+ n)) (q (M ℕ.∸ N ℕ.+ m) (M ℕ.∸ N ℕ.+ n)) ⟩
  ℚ.½ ℚ.* ε ℚ.+ ℚ.½ ℚ.* ε ≡˘⟨ ℚ.*-distribʳ-+ ε ℚ.½ ℚ.½ ⟩
  1ℚ ℚ.* ε ≡⟨ ℚ.*-identityˡ ε ⟩
  ε ∎
  where
    M = proj₁ (xs-cauchy (ℚ.½ ℚ.* ε) (ℚ.pos*pos ℚ.½ ε _ ε-positive))
    p = proj₂ (xs-cauchy (ℚ.½ ℚ.* ε) (ℚ.pos*pos ℚ.½ ε _ ε-positive))
    N = proj₁ (ys-cauchy (ℚ.½ ℚ.* ε) (ℚ.pos*pos ℚ.½ ε _ ε-positive))
    q = proj₂ (ys-cauchy (ℚ.½ ℚ.* ε) (ℚ.pos*pos ℚ.½ ε _ ε-positive))
    open ℚ.≤-Reasoning

_+_ : ℝ → ℝ → ℝ
x + y = record
  { sequence = +-sequence (ℝ.sequence x) (ℝ.sequence y)
  ; cauchy   = +-cauchy (ℝ.cauchy x) (ℝ.cauchy y)
  }
