{-# OPTIONS --safe --without-K #-}

module RationalExtras where

open import Data.Rational.Base
open import Data.Rational.Properties

-- this should be in Data.Rational.Properties
pos*pos : ∀ x y → Positive x → Positive y → Positive (x * y)
pos*pos x y x-positive y-positive = positive (begin-strict
  0ℚ     ≡˘⟨ *-zeroʳ x ⟩
  x * 0ℚ <⟨ *-monoʳ-<-pos x x-positive (positive⁻¹ {y} y-positive) ⟩
  x * y  ∎)
  where open ≤-Reasoning

