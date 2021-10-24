{-# OPTIONS --safe --without-K --guardedness #-}
module Stream where

open import Data.Nat.Base
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c

record Stream {a} (A : Set a) : Set a where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

drop : ℕ → Stream A → Stream A
drop zero xs = xs
drop (suc n) xs = drop n (tail xs)

_!_ : Stream A → ℕ → A
xs ! zero = head xs
xs ! suc n = tail xs ! n

repeat : A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

repeat-! : ∀ (x : A) n → repeat x ! n ≡ x
repeat-! x zero    = refl
repeat-! x (suc n) = repeat-! x n

map : (A → B) → Stream A → Stream B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

zipWith : (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

map-! : ∀ (f : A → B) (xs : Stream A) n → map f xs ! n ≡ f (xs ! n)
map-! f xs zero = refl
map-! f xs (suc n) = map-! f (tail xs) n

zipWith-! : ∀ (f : A → B → C) (xs : Stream A) (ys : Stream B) n → zipWith f xs ys ! n ≡ f (xs ! n) (ys ! n)
zipWith-! f xs ys zero = refl
zipWith-! f xs ys (suc n) = zipWith-! f (tail xs) (tail ys) n

record PW (_R_ : REL A B ℓ) (xs : Stream A) (ys : Stream B) : Set ℓ where
  coinductive
  field
    head : head xs R head ys
    tail : PW _R_ (tail xs) (tail ys)

open PW

map-repeat : ∀ (f : A → B) (x : A) → PW _≡_ (map f (repeat x)) (repeat (f x))
head (map-repeat f x) = refl
tail (map-repeat f x) = map-repeat f x
