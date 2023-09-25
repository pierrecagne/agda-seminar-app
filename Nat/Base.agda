{-# OPTIONS --without-K #-}

module Nat.Base where

open import Agda.Builtin.Equality
open import Equality.Base
open import Agda.Builtin.Sigma renaming (fst to π₁ ; snd to π₂)
open import Agda.Builtin.Nat
  using (zero ; _+_)
  renaming (Nat to ℕ ; suc to succ ; _*_ to _×_) public


{- recognizing succ as adding 1 -}

succ≡+1 : ∀ n → (succ n) ≡ (n + 1)
succ≡+1 zero = refl
succ≡+1 (succ n) = [ succ ] (succ≡+1 n)

{- associativity of succ -}

succ-ass : ∀ p q → (p + succ q) ≡ succ (p + q)
succ-ass zero q = refl
succ-ass (succ p) q = [ succ ] succ-ass p q

{- associativity of addition -}

ass-of-+ : ∀ n m p → ((n + m) + p) ≡ (n + (m + p))
ass-of-+ zero m p = refl
ass-of-+ (succ n) m p = [ succ ] (ass-of-+ n m p)


{- commutativity of addition -}

commutativity-of-+ : ∀ n m → (n + m) ≡ (m + n)
commutativity-of-+ zero zero = refl
commutativity-of-+ zero (succ m) =
  [ succ ] commutativity-of-+ 0 m
commutativity-of-+ (succ n) zero =
  [ succ ] commutativity-of-+ n 0
commutativity-of-+ (succ n) (succ m) =
  [ succ ] ((succ-ass n m) ∙ (commutativity-of-+ (succ n) m))


{- 0 is neutral on the right for the addition -}

0-neutral-+ : ∀ {m} → m + 0 ≡ m
0-neutral-+ {0} = refl
0-neutral-+ {succ m} = [ succ ] 0-neutral-+


{- 0 is absorbant for multiplication -}

0-absorption : ∀ m → (m × 0) ≡ 0
0-absorption 0 = refl
0-absorption (succ m) = 0-absorption m

{- expand multiplication relatively to succ -}

succ-exp : ∀ n m → (m × succ n) ≡ ((m × n) + m)
succ-exp n 0 = refl
succ-exp n (succ m) =
  ([ succ ] (([ (λ x → n + x) ] succ-exp n m) ∙ (sym (ass-of-+ n (m × n) m))))
  ∙ (sym (succ-ass (n + (m × n)) m))

{- commutativity of multiplication -}

commutativity-of-× : ∀ n m → (n × m) ≡ (m × n)
commutativity-of-× 0 m = sym (0-absorption m)
commutativity-of-× (succ n) m =
  (([ (λ x → m + x) ] commutativity-of-× n m)
  ∙ commutativity-of-+ m (m × n) )
  ∙ sym (succ-exp n m)


{- ℕ is a set -}

module _ where
  T : ∀ {n m : ℕ} (p : n ≡ m) → Set 
  T {zero} {zero} p = refl ≡ p
  T {succ n} {succ m} p = Σ (n ≡ m) (λ q → [ succ ] q ≡ p)
  
  sec-T : ∀ {n m : ℕ} (p : n ≡ m) → T p
  sec-T {zero} {.zero} refl = refl
  sec-T {succ m} {.(succ m)} refl = refl , refl
  
ℕ-set : ∀ {n m : ℕ} (p q : n ≡ m) → p ≡ q 
ℕ-set {zero} {.zero} refl q = sec-T q
ℕ-set {succ n} {.(succ n)} refl q =
  let (q' , r) = sec-T q in
  ([ ([_]_ succ) ] (ℕ-set refl q')) ∙ r
