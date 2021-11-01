{-# OPTIONS --allow-unsolved-metas #-}

open import Tutorials.Monday
open import Tutorials.Tuesday
module Tutorials.Wednesday where

-----------
-- Interfaces, isomorphisms
-----------

module Isomorphism where
  -- Why can we import _,_ from both modules without resulting in a nameclash?
  open Simple using (_⊎_; _×_; _,_; inl; inr)
  open Product using (Σ-syntax; Σ-⊎; Σ-×; Π-×; Π-→; _,_)
  open Fin using (Fin; zero; suc)

  infix 2 _≅_
  record _≅_ (A B : Set) : Set where
    constructor Mk≅
    field
      to      : A → B
      from    : B → A
      from∘to : ∀ a → from (to a) ≡ a
      to∘from : ∀ b → to (from b) ≡ b

  open _≅_

  Σ-⊎-≅ : Σ-⊎ A B ≅ A ⊎ B
  Σ-⊎-≅ = {!!}

  Σ-×-≅ : Σ-× A B ≅ A × B
  Σ-×-≅ = {!!}

  Π-→-≅ : Π-→ A B ≅ (A → B)
  to Π-→-≅ = {!!}
  from Π-→-≅ = {!!}
  -- Needs η laws for functions (∀ x → f x) ≡ f
  from∘to Π-→-≅ = {!!}
  to∘from Π-→-≅ = {!!}

  -- The following isomorphism needs of function extensionality
  -- Function extensionality claims that if two functions give the same output on the same input, then they are equal
  -- Agda is an intensional type theory, and thus this does not hold internally
  -- We therefore need to postulate it as an axiom
  postulate
    extensionality : {P : A → Set} {f g : (a : A) → P a} → (∀ x → f x ≡ g x) → f ≡ g

  Π-×-≅ : Π-× A B ≅ A × B
  to Π-×-≅ = {!!}
  from Π-×-≅ = {!!}
  from∘to Π-×-≅ = {!!}
  to∘from Π-×-≅ = {!!}

  Fin-≤-≅ : Fin m ≅ Σ[ n ∈ ℕ ] n < m
  to Fin-≤-≅ = {!!}
  from Fin-≤-≅ = {!!}
  from∘to Fin-≤-≅ = {!!}
  to∘from Fin-≤-≅ = {!!}


-----------
-- Decidability
-----------

module Dec where
  open Fin
  open Product using (_×_; _,_; fst; snd; curry)
  open Simple using (¬_)

  data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

  map : (A → B) → (¬ A → B) → Dec A → B
  map f g (yes x) = f x
  map f g (no x) = g x

  infix 5 _×-dec_
  _×-dec_ : Dec A → Dec B → Dec (A × B)
  yes x ×-dec yes y = yes (x , y)
  yes x ×-dec no ¬y = no (¬y ∘ snd)
  no ¬x ×-dec B? = no (¬x ∘ fst)

  _ℕ-≟_ : (n m : ℕ) → Dec (n ≡ m)
  n ℕ-≟ m = {!!}

  suc-injective : {i j : Fin n} → _≡_ {A = Fin (suc n)} (suc i) (suc j) → i ≡ j
  suc-injective refl = refl

  _Fin-≟_ : (i j : Fin n) → Dec (i ≡ j)
  zero Fin-≟ zero = yes refl
  zero Fin-≟ suc j = no λ ()
  suc i Fin-≟ zero = no λ ()
  suc i Fin-≟ suc j = map (yes ∘ cong suc) (λ neq → no (neq ∘ suc-injective)) (i Fin-≟ j)

  open List using (List; []; _∷_)

  ∷-injective : {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-injective refl = refl , refl

  List-≟ : (_A-≟_ : (x y : A) → Dec (x ≡ y)) → (xs ys : List A) → Dec (xs ≡ ys)
  List-≟ _A-≟_ [] [] = yes refl
  List-≟ _A-≟_ [] (y ∷ ys) = no λ ()
  List-≟ _A-≟_ (x ∷ xs) [] = no λ ()
  List-≟ _A-≟_ (x ∷ xs) (y ∷ ys) = map (yes ∘ curry (cong₂ _∷_)) (no ∘ (λ neq → neq ∘ ∷-injective)) (x A-≟ y ×-dec List-≟ _A-≟_ xs ys)

-----------
-- Interfaces
-----------

module Monoid where
  open Fin
  open List using (List; []; _∷_; _++_)
  open Vec using (Vec; []; _∷_; _!_)

  -- We define what it is to be a monoid on a carrier set C
  record Monoid (C : Set) : Set where
    constructor MkMonoid
    field
      ε   : C
      _∙_ : C → C → C
      -- Including the algebraic laws
      idˡ : (x : C) → ε ∙ x ≡ x
      idʳ : (x : C) → x ∙ ε ≡ x
      assoc : (x y z : C) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  -- The syntax for an expression tree of symbolic monoidal operations
  infixl 20 _‵∙_
  infix 25 ‵_
  data Expr : ℕ → Set where
    ‵_ : Fin n → Expr n
    ‵ε : Expr n
    _‵∙_ : Expr n → Expr n → Expr n

  -- And define equations on monoids
  infix 10 _‵≡_
  record Eqn (n : ℕ) : Set where
    constructor _‵≡_
    field
      lhs : Expr n
      rhs : Expr n

  -- The canonical normal form for expression trees
  NormalForm : ℕ → Set
  NormalForm n = List (Fin n)

  normalise : Expr n → NormalForm n
  normalise (‵ x) = x ∷ []
  normalise ‵ε = []
  normalise (xs ‵∙ ys) = normalise xs ++ normalise ys

  module Eval (M : Monoid C) where
    open Monoid M

    -- An environment maps symbols to values in the carrier set
    Env : ℕ → Set
    Env n = Vec C n

    -- Evaluate the syntax in a given environment
    ⟦_⟧ : Expr n → Env n → C
    ⟦ ‵ x ⟧ Γ = Γ ! x
    ⟦ ‵ε ⟧ Γ = ε
    ⟦ x ‵∙ y ⟧ Γ = ⟦ x ⟧ Γ ∙ ⟦ y ⟧ Γ

    -- Evaluate the normal form in a given environment
    ⟦_⟧⇓ : NormalForm n → Env n → C
    ⟦ [] ⟧⇓ Γ = ε
    ⟦ x ∷ xs ⟧⇓ Γ = (Γ ! x) ∙ ⟦ xs ⟧⇓ Γ

    -- The evaluation of normal forms distributes over list concatenation
    ++-homo : ∀ Γ (xs ys : NormalForm n) → ⟦ xs ++ ys ⟧⇓ Γ ≡ ⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ
    ++-homo Γ [] ys = sym (idˡ _)
    ++-homo Γ (x ∷ xs) ys = begin
      (Γ ! x) ∙ ⟦ xs ++ ys ⟧⇓ Γ
        ≡⟨ cong (_ ∙_) (++-homo Γ xs ys) ⟩
      (Γ ! x) ∙ (⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ)
        ≡⟨ sym (assoc _ _ _) ⟩
      ((Γ ! x) ∙ ⟦ xs ⟧⇓ Γ) ∙ ⟦ ys ⟧⇓ Γ
        ∎

    -- Normalising and then evaluating the normal form is equal to evaluating the original expression
    correct : ∀ Γ (expr : Expr n) → ⟦ normalise expr ⟧⇓ Γ ≡ ⟦ expr ⟧ Γ
    correct Γ (‵ x) = idʳ _
    correct Γ ‵ε = refl
    correct Γ (le ‵∙ re) = begin
      ⟦ normalise le ++ normalise re ⟧⇓ Γ
        ≡⟨ ++-homo Γ (normalise le) (normalise re) ⟩
      (⟦ normalise le ⟧⇓ Γ ∙ ⟦ normalise re ⟧⇓ Γ)
        ≡⟨ cong₂ _∙_ (correct Γ le) (correct Γ re) ⟩
      (⟦ le ⟧ Γ ∙ ⟦ re ⟧ Γ)
        ∎

    -- We describe what it is to be a solution to an equation
    -- If both sides normalise to the same symbols in the same order,
    -- we claim that the monoid laws make the equations hold in any environment
    Solution : Eqn n → Set
    Solution (lhs ‵≡ rhs) =
      Dec.map
        -- Both sides normalise to a common list of symbols, we must now show that the equation holds under any environment
        (λ _ → ∀ (Γ : Env _) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
        -- Both sides do *not* normalise to a common list of symbols, we claim only the trivial
        (λ _ → ⊤)
        (Dec.List-≟ Dec._Fin-≟_ (normalise lhs) (normalise rhs))

    -- Now that we have described what a solution is, we show that we can provide one
    solve : (eqn : Eqn n) → Solution eqn
    -- Pattern matching using with makes the goal type compute
    solve (lhs ‵≡ rhs) with Dec.List-≟ Dec._Fin-≟_ (normalise lhs) (normalise rhs)
    solve (lhs ‵≡ rhs) | Dec.no _ = tt
    solve (lhs ‵≡ rhs) | Dec.yes lhs⇓≡rhs⇓ = λ Γ → begin
      ⟦ lhs ⟧ Γ            ≡⟨ sym (correct Γ lhs) ⟩
      ⟦ normalise lhs ⟧⇓ Γ ≡⟨ cong (λ ● → ⟦ ● ⟧⇓ Γ) lhs⇓≡rhs⇓ ⟩
      ⟦ normalise rhs ⟧⇓ Γ ≡⟨ correct Γ rhs ⟩
      ⟦ rhs ⟧ Γ
        ∎

  -- An example instance of a monoid: natural numbers with addition
  NAT-MONOID : Monoid ℕ
  Monoid.ε NAT-MONOID = zero
  Monoid._∙_ NAT-MONOID = _+_
  Monoid.idˡ NAT-MONOID = +-idˡ
  Monoid.idʳ NAT-MONOID = +-idʳ
  Monoid.assoc NAT-MONOID = +-assoc

  -- An example usage of the monoid solver
  -- We first need to "quote" the goal, i.e. describe it in terms of the expression language / syntax
  -- NAT-MONOID describes how to interpret the syntax back and evaluate the expression into a value of the carrier set
  eqn₁-auto : (x y z : ℕ) → (0 + x) + y + (y + z) ≡ x + (0 + y + 0) + (y + z + 0)
  eqn₁-auto x y z =
    let
      ‵x = zero
      ‵y = suc zero
      ‵z = suc (suc zero)
      lhs = (‵ε ‵∙ ‵ ‵x) ‵∙ ‵ ‵y ‵∙ (‵ ‵y ‵∙ ‵ ‵z)
      rhs = ‵ ‵x ‵∙ (‵ε ‵∙ ‵ ‵y ‵∙ ‵ε) ‵∙ (‵ ‵y ‵∙ ‵ ‵z ‵∙ ‵ε)
    in
    {!Eval.solve NAT-MONOID (lhs ‵≡ rhs) (x ∷ y ∷ z ∷ [])!}
