{-# OPTIONS --safe --without-K #-}
module RationalMetric where

open import Data.Rational.Base
open import Data.Rational.Properties

open import Function.Metric.Rational

open import Relation.Binary.PropositionalEquality

private
  neg-involutive : ∀ x → - - x ≡ x
  neg-involutive x = begin
      - - x ≡˘⟨ +-identityʳ (- - x) ⟩
      - - x + 0ℚ ≡˘⟨ cong (- - x +_) (+-inverseˡ x) ⟩
      - - x + (- x + x) ≡˘⟨ +-assoc (- - x) (- x) x ⟩
      (- - x - x) + x ≡⟨ cong (_+ x) (+-inverseˡ (- x)) ⟩
      0ℚ + x ≡⟨ +-identityˡ x ⟩
      x     ∎
    where open ≡-Reasoning

  ≈⇒0 : ∀ {x y} → x ≡ y → ∣ x - y ∣ ≡ 0ℚ
  ≈⇒0 {x} {y} x≡y = begin
    ∣ x - y ∣ ≡⟨ cong (λ x′ → ∣ x′ - y ∣) x≡y ⟩
    ∣ y - y ∣ ≡⟨ cong ∣_∣ (+-inverseʳ y) ⟩
    0ℚ        ∎
    where open ≡-Reasoning

  0⇒≈ : ∀ {x y} → ∣ x - y ∣ ≡ 0ℚ → x ≡ y
  0⇒≈ {x} {y} ∣x-y∣≡0 = begin
    x ≡˘⟨ +-identityʳ x ⟩
    x - 0ℚ ≡˘⟨ cong (λ k → x - k) (∣p∣≡0⇒p≡0 (x - y) ∣x-y∣≡0) ⟩
    x - (x - y) ≡⟨ cong (x +_) (neg-distrib-+ x (- y)) ⟩
    x + (- x - - y) ≡˘⟨ +-assoc x (- x) (- - y) ⟩
    x - x - - y ≡⟨ cong (x - x +_) (neg-involutive y) ⟩
    x - x + y ≡⟨ refl ⟩
    (x - x) + y ≡⟨ cong (_+ y) (+-inverseʳ x) ⟩
    0ℚ + y ≡⟨ +-identityˡ y ⟩
    y ∎
    where open ≡-Reasoning

  L₀-sym : ∀ x y → ∣ x - y ∣ ≡ ∣ y - x ∣
  L₀-sym x y = begin
    ∣ x - y ∣ ≡˘⟨ ∣-p∣≡∣p∣ (x - y) ⟩
    ∣ - (x - y) ∣ ≡⟨ cong ∣_∣ (neg-distrib-+ x (- y)) ⟩
    ∣ - x - - y ∣ ≡⟨ cong (λ k → ∣ - x + k ∣) (neg-involutive y) ⟩
    ∣ - x + y ∣ ≡⟨ cong ∣_∣ (+-comm (- x) y) ⟩
    ∣ y - x ∣ ∎
    where open ≡-Reasoning

  triangle : ∀ x y z → ∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣
  triangle x y z = begin
    ∣ x - z ∣             ≡˘⟨ cong (λ k → ∣ k - z ∣) (+-identityʳ x) ⟩
    ∣ x + 0ℚ - z ∣        ≡˘⟨ cong (λ k → ∣ x + k - z ∣) (+-inverseˡ y) ⟩
    ∣ x + (- y + y) - z ∣ ≡˘⟨ cong (λ k → ∣ k - z ∣) (+-assoc x (- y) y) ⟩
    ∣ (x - y) + y - z ∣   ≡⟨ cong ∣_∣ (+-assoc (x - y) y (- z)) ⟩
    ∣ (x - y) + (y - z) ∣ ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (x - y) (y - z) ⟩
    ∣ x - y ∣ + ∣ y - z ∣ ∎
    where open ≤-Reasoning

∣x-y∣-isMetric : IsMetric _≡_ (λ x y → ∣ x - y ∣)
∣x-y∣-isMetric = record
  { isSemiMetric = record
    { isQuasiSemiMetric = record
      { isPreMetric = record
        { isProtoMetric = record
          { isPartialOrder = ≤-isPartialOrder
          ; ≈-isEquivalence = isEquivalence
          ; cong = cong₂ (λ x y → ∣ x - y ∣)
          ; nonNegative = λ {x} {y} → 0≤∣p∣ (x - y)
          }
        ; ≈⇒0 = ≈⇒0
        }
      ; 0⇒≈ = 0⇒≈
      }
    ; sym = L₀-sym
    }
  ; triangle = triangle
  }
