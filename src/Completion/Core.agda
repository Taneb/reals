{-# OPTIONS --safe --without-K --guardedness #-}

open import Function.Metric.Rational.Core

module Completion.Core {a} {A : Set a} (d : DistanceFunction A) where

import Data.Nat.Base as ℕ
open import Data.Rational.Base
open import Data.Product

open import Stream

IsCauchy : Stream A → Set _
IsCauchy seq = ∀ ε → Positive ε → ∃[ N ] ∀ m n → d (seq ! (N ℕ.+ m)) (seq ! (N ℕ.+ n)) < ε
