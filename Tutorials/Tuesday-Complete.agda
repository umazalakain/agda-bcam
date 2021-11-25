open import Tutorials.Monday-Complete
module Tutorials.Tuesday-Complete where

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
  Π : (A : Set) → (Pred A) → Set
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

  example₁ : Σ ℕ EvenData
  example₁ = 0 , zero

  one-is-not-even : ¬ EvenData 1
  one-is-not-even ()

  example₂ : ¬ Π ℕ EvenData
  example₂ f = one-is-not-even (f 1)


  ¬∘ : Pred A → Pred A
  ¬∘ P = ¬_ ∘ P

  -- These can be proven regardless of A

  ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬∘ P)
  ¬∃⇒∀¬ f x px = f (x , px)

  ∃¬⇒¬∀ : Σ A (¬∘ P) → ¬ Π A P
  ∃¬⇒¬∀ (a , ¬pa) f = ¬pa (f a)

  ∀¬⇒¬∃ : Π A (¬∘ P) → ¬ Σ A P
  ∀¬⇒¬∃ f (a , pa) = f a pa

  -- Works in classical, not in constructive mathematics
  postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬∘ P)

  -- Show that ≤ is antisymmetric
  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ z≤n z≤n = refl
  ≤-≡ (s≤s x) (s≤s y) = cong suc (≤-≡ x y)

  -- By using n ≤ m instead of Fin m we can mention n in the output
  take : Vec A m → n ≤ m → Vec A n
  take xs z≤n = []
  take (x ∷ xs) (s≤s lte) = x ∷ take xs lte

  Fin-to-≤ : (i : Fin m) → to-ℕ i < m
  Fin-to-≤ zero = s≤s z≤n
  Fin-to-≤ (suc i) = s≤s (Fin-to-≤ i)

  -- Proof combining sigma types and equality
  ≤-to-Fin : n < m → Fin m
  ≤-to-Fin (s≤s z≤n) = zero
  ≤-to-Fin (s≤s (s≤s i)) = suc (≤-to-Fin (s≤s i))

  Fin-≤-inv : (i : Fin m) → ≤-to-Fin (Fin-to-≤ i) ≡ i
  Fin-≤-inv zero = refl
  Fin-≤-inv (suc zero) = refl
  Fin-≤-inv (suc (suc i)) = cong suc (Fin-≤-inv (suc i))

  ≤-Fin-inv : (lt : Σ[ n ∈ ℕ ] n < m)
            → (to-ℕ (≤-to-Fin (snd lt)) , Fin-to-≤ (≤-to-Fin (snd lt))) ≡ lt
  ≤-Fin-inv (.zero , s≤s z≤n) = refl
  ≤-Fin-inv (.(suc _) , s≤s (s≤s i)) =
    cong (map suc s≤s) (≤-Fin-inv (_ , s≤s i))
