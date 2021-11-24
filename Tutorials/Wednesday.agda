{-# OPTIONS --allow-unsolved-metas #-}

open import Tutorials.Monday-Complete
open import Tutorials.Tuesday
open List using (List; []; _∷_; _++_)
open Vec using (Vec; []; _∷_; _!_)
open Fin using (Fin; zero; suc)
module Tutorials.Wednesday where

-----------
-- Interfaces, isomorphisms
-----------

module Isomorphism where
  -- Why can we import _,_ from both modules without resulting in a nameclash?
  open Simple using (_⊎_; _×_; _,_; inl; inr)
  open Product using (Σ-syntax; Σ-⊎; Σ-×; Π-×; Π-→; _,_)

  infix 2 _≅_
  record _≅_ (A B : Set) : Set where
    constructor Mk≅
    field
      to      : A → B
      from    : B → A
      from∘to : ∀ a → from (to a) ≡ a
      to∘from : ∀ b → to (from b) ≡ b

  open _≅_

  -- We can use copattern matching to construct a record by defining how to construct each of its fields
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
  -- This does not hold internally in Agda and we therefore need to postulate it as an axiom
  postulate
    extensionality : {P : A → Set} {f g : (a : A) → P a} → (∀ x → f x ≡ g x) → f ≡ g

  Π-×-≅ : Π-× A B ≅ A × B
  Π-×-≅ = {!!}

  curry : Π-→ A (Π-→ B C) → Π-→ (Σ-× A B) C
  curry f (a , b) = f a b

  uncurry : Π-→ (Σ-× A B) C → Π-→ A (Π-→ B C)
  uncurry f a b = f (a , b)

  curry-uncurry : Π-→ A (Π-→ B C) ≅ Π-→ (Σ-× A B) C
  curry-uncurry = {!!}

  Fin-≤-≅ : Fin m ≅ Σ[ n ∈ ℕ ] n < m
  Fin-≤-≅ = {!!}

  _iso-∘_ : B ≅ C → A ≅ B → A ≅ C
  x iso-∘ y = {!!}

-----------
-- Decidability
-----------

module Dec where
  open Product using (_×_; _,_; fst; snd)
  open Simple using (¬_)

  data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

  DecEq : Set → Set
  DecEq A = (x y : A) → Dec (x ≡ y)

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
  suc i Fin-≟ suc j = map
    (yes ∘ cong suc)
    (no ∘ (λ neq → neq ∘ suc-injective))
    (i Fin-≟ j)

  ∷-injective : {x y : A} {xs ys : List A} → _≡_ {A = List A} (x ∷ xs) (y ∷ ys) → x ≡ y × xs ≡ ys
  ∷-injective refl = refl , refl

  List-≟ : (_A-≟_ : (x y : A) → Dec (x ≡ y)) → (xs ys : List A) → Dec (xs ≡ ys)
  List-≟ _A-≟_ [] [] = yes refl
  List-≟ _A-≟_ [] (y ∷ ys) = no λ ()
  List-≟ _A-≟_ (x ∷ xs) [] = no λ ()
  List-≟ _A-≟_ (x ∷ xs) (y ∷ ys) = map
    (yes ∘ Isomorphism.curry (cong₂ _∷_))
    (no ∘ (λ neq → neq ∘ ∷-injective))
    (x A-≟ y ×-dec List-≟ _A-≟_ xs ys)

-----------
-- Interfaces
-----------

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

module MonoidSolver (Symbol : Set) (symbol-≟ : Dec.DecEq Symbol) where
  -- The syntax for an expression tree of symbolic monoidal operations
  infixl 20 _‵∙_
  infix 25 ‵_
  data Expr : Set where
    ‵ε   : Expr
    ‵_   : Symbol → Expr
    _‵∙_ : Expr → Expr → Expr

  -- And define equations on monoids
  infix 10 _‵≡_
  record Eqn : Set where
    constructor _‵≡_
    field
      lhs : Expr
      rhs : Expr

  -- The canonical normal form for expression trees
  NormalForm : Set
  NormalForm = List Symbol

  normalise : Expr → NormalForm
  normalise ‵ε = []
  normalise (‵ x) = x ∷ []
  normalise (xs ‵∙ ys) = normalise xs ++ normalise ys

  module Eval (M : Monoid C) where
    open Monoid M

    -- An environment maps symbols to values in the carrier set
    Env : Set
    Env = Symbol → C

    -- Evaluate the syntax in a given environment
    ⟦_⟧ : Expr → Env → C
    ⟦ ‵ε ⟧ Γ = ε
    ⟦ ‵ x ⟧ Γ = Γ x
    ⟦ x ‵∙ y ⟧ Γ = ⟦ x ⟧ Γ ∙ ⟦ y ⟧ Γ

    -- Evaluate the normal form in a given environment
    ⟦_⟧⇓ : NormalForm → Env → C
    ⟦ [] ⟧⇓ Γ = ε
    ⟦ x ∷ xs ⟧⇓ Γ = Γ x ∙ ⟦ xs ⟧⇓ Γ

    -- The evaluation of normal forms distributes over list concatenation
    ++-homo : ∀ Γ (xs ys : NormalForm) → ⟦ xs ++ ys ⟧⇓ Γ ≡ ⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ
    ++-homo Γ [] ys = sym (idˡ _)
    ++-homo Γ (x ∷ xs) ys = begin
      Γ x ∙ ⟦ xs ++ ys ⟧⇓ Γ
        ≡⟨ cong (_ ∙_) (++-homo Γ xs ys) ⟩
      Γ x ∙ (⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ)
        ≡⟨ sym (assoc _ _ _) ⟩
      (Γ x ∙ ⟦ xs ⟧⇓ Γ) ∙ ⟦ ys ⟧⇓ Γ
        ∎

    -- Normalising and then evaluating the normal form is equal to evaluating the original expression
    correct : ∀ Γ (expr : Expr) → ⟦ normalise expr ⟧⇓ Γ ≡ ⟦ expr ⟧ Γ
    correct Γ ‵ε = refl
    correct Γ (‵ x) = idʳ _
    correct Γ (le ‵∙ re) = begin
      ⟦ normalise le      ++  normalise re ⟧⇓ Γ ≡⟨ ++-homo Γ (normalise le) (normalise re) ⟩
      ⟦ normalise le ⟧⇓ Γ ∙ ⟦ normalise re ⟧⇓ Γ ≡⟨ cong₂ _∙_ (correct Γ le) (correct Γ re) ⟩
      ⟦ le ⟧            Γ ∙ ⟦ re ⟧            Γ ∎

    -- We describe what it is to be a solution to an equation
    -- If both sides normalise to the same symbols in the same order,
    -- we claim that the monoid laws make the equations hold in any environment
    Solution : Eqn → Set
    Solution (lhs ‵≡ rhs) =
      Dec.map
        -- Both sides normalise to a common list of symbols, we must now show that the equation holds under any environment
        (λ _ → ∀ (Γ : Env) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
        -- Both sides do *not* normalise to a common list of symbols, we claim only the trivial
        (λ _ → ⊤)
        (Dec.List-≟ symbol-≟ (normalise lhs) (normalise rhs))

    -- Now that we have described what a solution is, we show that we can provide one
    solve : (eqn : Eqn) → Solution eqn
    -- Pattern matching using with makes the goal type compute
    solve (lhs ‵≡ rhs) with Dec.List-≟ symbol-≟ (normalise lhs) (normalise rhs)
    solve (lhs ‵≡ rhs) | Dec.no _ = tt
    solve (lhs ‵≡ rhs) | Dec.yes lhs⇓≡rhs⇓ = λ Γ → begin
      ⟦ lhs ⟧ Γ            ≡⟨ sym (correct Γ lhs) ⟩
      ⟦ normalise lhs ⟧⇓ Γ ≡⟨ cong (λ ● → ⟦ ● ⟧⇓ Γ) lhs⇓≡rhs⇓ ⟩
      ⟦ normalise rhs ⟧⇓ Γ ≡⟨ correct Γ rhs ⟩
      ⟦ rhs ⟧ Γ            ∎

open MonoidSolver

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
  Eval.solve (Fin 3) Dec._Fin-≟_ NAT-MONOID (lhs ‵≡ rhs) λ where
    zero → x
    (suc zero) → y
    (suc (suc zero)) → z
