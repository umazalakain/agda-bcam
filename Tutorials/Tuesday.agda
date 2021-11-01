{-# OPTIONS --allow-unsolved-metas #-}

open import Tutorials.Monday
module Tutorials.Tuesday where

-----------
-- Pi and Sigma types
-----------

module Product where
  -- The open keyword opens a given module in the current namespace
  -- By default all of the public names of the module are opened
  -- The using keyword limits the imported definitions to those explicitly listed
  open Fin
  open Vec using (Vec; []; _∷_)
  open Simple using (¬_)

  variable
    P Q : A → Set

  -- Pi types: dependent function types
  -- For every x of type A, the predicate P x holds
  Π : (A : Set) → (A → Set) → Set
  Π A P = (x : A) → P x

  infix 5 _,_
  -- Sigma types: dependent product types, existential types
  -- For this x of type A, the predicate P x holds
  record Σ (A : Set) (P : Pred A) : Set where
    -- In the type P fst, fst refers to a previously introduced field
    constructor _,_
    field
      fst : A
      snd : P fst

  open Σ public

  -- By depending on a boolean we can use pi types to represent product types
  Π-× : Set → Set → Set
  Π-× A B = Π Bool λ where
    true  → A
    false → B

  -- By depending on a boolean we can use sigma types to represent sum types
  Σ-⊎ : Set → Set → Set
  Σ-⊎ A B = Σ Bool λ where
    true  → A
    false → B

  -- Use pi types to recover function types
  Π-→ : Set → Set → Set
  Π-→ A B = Π A λ where
    _     → B

  -- Use sigma types to recover product types
  Σ-× : Set → Set → Set
  Σ-× A B = Σ A λ where
    _     → B

  infix 5 _×_
  _×_ : Set → Set → Set
  _×_ = Σ-×

  curry : (A → B → C) → (A × B → C)
  curry f (a , b) = f a b

  -- 1) If we can transform the witness and
  -- 2) transform the predicate as per the transformation on the witness
  -- ⇒) then we can transform a sigma type
  map : (f : A → B) → (∀ {x} → P x → Q (f x)) → (Σ A P → Σ B Q)
  map f g (x , y) = (f x , g y)

  -- The syntax keyword introduces notation that can include binders
  infix 4 Σ-syntax
  Σ-syntax : (A : Set) → (A → Set) → Set
  Σ-syntax = Σ
  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  ¬∘ : Pred A → Pred A
  ¬∘ P = ¬_ ∘ P

  -- These can be proven regardless of A

  ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬∘ P)
  ¬∃⇒∀¬ = {!!}

  ∃¬⇒¬∀ : Σ A (¬∘ P) → ¬ Π A P
  ∃¬⇒¬∀ = {!!}

  ∀¬⇒¬∃ : Π A (¬∘ P) → ¬ Σ A P
  ∀¬⇒¬∃ = {!!}

  -- Works in classical, not in constructive mathematics
  -- Unless A is discrete, inhabited, and finite, and P is decidable
  postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬∘ P)

  -- Show that ≤ is antisymmetric
  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ x y = {!!}

  -- By using n ≤ m instead of Fin m we can mention n in the output
  take : Vec A m → n ≤ m → Vec A n
  take xs lte = {!!}

  -- Proof combining sigma types and equality
  Fin-to-≤ : (i : Fin m) → Σ[ n ∈ ℕ ] to-ℕ i ≡ n × n < m
  Fin-to-≤ i = {!!}

  ≤-to-Fin : n < m → Σ[ i ∈ Fin m ] to-ℕ i ≡ n
  ≤-to-Fin i = {!!}

