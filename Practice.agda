{-# OPTIONS --without-K --exact-split --safe #-}

module _ where

open import Agda.Primitive renaming (Level to Universe; lzero to 𝓤₀; lsuc to _⁺; Setω to 𝓤ω) using (_⊔_)

Type = λ ℓ → Set ℓ

_̇ : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇ = Type 𝓤
infix 1 _̇ 

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

variable
  𝓤 𝓥 𝓦 𝓣 : Universe

-- The one-element type 𝟙
data 𝟙 : 𝓤₀ ̇ where
  ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

-- The empty type 𝟘
data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

-- The type ℕ of natural numbers
data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction
  : (A : ℕ → 𝓤 ̇)
  → A 0
  → ((n : ℕ) → A n → A (succ n))
  → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
  h : (n : ℕ) → A n
  h 0 = a₀
  h (succ n) = f n (h n)

ℕ-recursion
  : (X : 𝓤 ̇)
  → X
  → (ℕ → X → X)
  → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration
  : (X : 𝓤 ̇)
  → X
  → (X → X)
  → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

