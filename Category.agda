module Category where

open import Agda.Builtin.Equality
open import Equality.Base
open import Agda.Builtin.Unit
open import Nat.Base
open import Agda.Builtin.Sigma

record Category : Set₁ where
  field
    -- structure
    Obj : Set
    Hom : Obj → Obj → Set
    id : ∀ (X : Obj) → Hom X X
    _∘_ : ∀ {X Y Z : Obj} → Hom Y Z → Hom X Y →  Hom X Z 

    -- axioms/rules
    idl : ∀ {X Y} (f : Hom X Y) → (id Y) ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ (id X) ≡ f
    assoc :
      ∀ {X Y Z W} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W) →
      (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)


𝟙 : Category
Category.Obj 𝟙 = ⊤ -- { ⋆ }
Category.Hom 𝟙 tt tt = ⊤ -- { id ⋆ }
Category.id 𝟙 tt = tt
Category._∘_ 𝟙 g f = tt
Category.idl 𝟙 _ = refl
Category.idr 𝟙 _ = refl
Category.assoc 𝟙 _ _ _ = refl

{- define the empty/initial category 𝟘 -}
data ⊥ : Set where

𝟘 : Category
Category.Obj 𝟘 = ⊥
Category.Hom 𝟘 ()
Category.id 𝟘 () 
Category._∘_ 𝟘 {()}
Category.idl 𝟘 {()}
Category.idr 𝟘 {()}
Category.assoc 𝟘 {()}

{-

define the category whose objects are the natural numbers, and
hom(n,m) = { k | n+k = m }, identities and compositions are the only thing they can be.

-}

Cayley-ℕ : Category
Category.Obj Cayley-ℕ = ℕ
Category.Hom Cayley-ℕ n m = Σ ℕ (λ k → n + k ≡ m)
Category.id Cayley-ℕ n = 0 , 0-neutral-+
Category._∘_ Cayley-ℕ (l , m+l≡p) (k , n+k≡m) =
  (k + l) , ((sym (ass-of-+ _ k l) ∙ ([ (λ x → x + l) ] n+k≡m )) ∙ m+l≡p)
Category.idl Cayley-ℕ (k , n+k≡m) = Σ≡ 0-neutral-+ (ℕ-set _ _)
Category.idr Cayley-ℕ = {!!}
Category.assoc Cayley-ℕ = {!!}
