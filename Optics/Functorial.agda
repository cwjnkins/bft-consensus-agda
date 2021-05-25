{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Level
open import Function
open import Category.Functor
open import Relation.Binary.PropositionalEquality

module Optics.Functorial where

  private
    variable
      ℓ : Level

  Lens' : (F : Set ℓ → Set ℓ) → RawFunctor F → Set ℓ → Set ℓ → Set ℓ
  Lens' F _ S A = (A → F A) → S → F S

  data Lens (S A : Set ℓ) : Set (Level.suc ℓ) where
    lens : ((F : Set ℓ → Set ℓ)(rf : RawFunctor F) → Lens' F rf S A)
         → Lens S A

  private
    cf : {A : Set ℓ} → RawFunctor {ℓ} (const A)
    cf = record { _<$>_ = λ x x₁ → x₁ }

    if : RawFunctor {ℓ} id
    if = record { _<$>_ = λ x x₁ → x x₁ }

  -- We can make lenses relatively painlessly without requiring reflection
  -- by providing getter and setter functions
  mkLens' : ∀ {A B : Set ℓ} → (get : B → A) (set : B → A → B) → Lens B A
  mkLens' {S} {A} get set =
    lens λ F rf f b →
      Category.Functor.RawFunctor._<$>_ rf (set b) (f (get b))

  -- Getter:

  -- this is typed as ^\.
  _^∙_ : ∀ {S A : Set ℓ} → S → Lens S A → A
  _^∙_ {A = A} s (lens p) = p (const A) cf id s

  -- Setter:

  set : ∀ {S A : Set ℓ} → Lens S A → A → S → S
  set (lens p) a s = p id if (const a) s
  syntax set p a s = s [ p := a ]

  -- Modifier:

  over : ∀ {S A : Set ℓ} → Lens S A → (A → A) → S → S
  over (lens p) f s = p id if f s
  syntax over p f s = s [ p %~ f ]


  -- Composition

  infixr 30 _∙_
  _∙_ : ∀ {S A B : Set ℓ} → Lens S A → Lens A B → Lens S B
  (lens p) ∙ (lens q) = lens (λ F rf x x₁ → p F rf (q F rf x) x₁)
