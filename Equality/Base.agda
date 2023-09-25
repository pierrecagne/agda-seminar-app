{-# OPTIONS --without-K #-}

module Equality.Base where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

{- transport -}

trp :
  ∀ {A : Set} (B : A → Set) {a a' : A}
  (b : B a) → (a ≡ a') → B a'
trp B b refl = b

{- path concatenation -}

_∙_ :
  ∀ {A : Set} {a₁ a₂ a₃ : A} →
  (a₁ ≡ a₂) → (a₂ ≡ a₃) → (a₁ ≡ a₃)
refl ∙ q = q

{- path inversion -}

sym : ∀ {A : Set} {a₁ a₂ : A} → (a₁ ≡ a₂) → (a₂ ≡ a₁)
sym refl = refl

{- function application -}

[_]_ :
  ∀ {A B : Set} (f : A → B) →
  ∀ {a a' : A} → (a ≡ a') → (f a) ≡ (f a')
[ f ] refl = refl


{- pairs of equalities built equalities of pairs -}

Σ≡ :
  ∀ {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} →
  ∀ (p : a ≡ a') → trp B b p ≡ b' → (a , b) ≡ (a' , b')
Σ≡ refl refl = refl
