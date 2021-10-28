{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (Level)
module Tutorials.Monday where


-- two dashes to comment out the rest of the line
{-
  opening {- and closing -} for a
  multi-line comment
-}


data ⊥ : Set where -- AKA the empty set, bottom, falsehood, the absurd type, the empty type, the initial element
  -- : declares the type of something
  -- Zero : Set means Zero is a Type (Set = Type, for historical reasons)
  -- data creates a data type
  -- we list all of its constructors, all the ways in which we can make a Zero
  -- no constructors: no way of making a Zero

record ⊤ : Set where -- AKA the singleton set, top, truth, the trivial type, the unit type, the terminal element
  -- record creates a record type
  -- records have a single constructor
  -- to create a record you must populate all of its fields
  -- One has no fields: it's trivial to make one
  -- zero bits worth of information
  constructor tt

data Bool : Set where -- one bit
  true : Bool
  false : Bool

--------
-- Simple composite types
--------

infix 5 _×_ _,_
record _×_ (A : Set) (B : Set) : Set where -- AKA logical and, product type
  -- introduce unicode
  -- introduce misfix notation
  -- introduce tokenisation by spacing
  -- a type packing up an A and a B
  -- A and B are type parameters
  -- fst and snd are fields
  -- each fields has a type, the type of fst is A, the type of snd is B
  -- to make something of type A × B, one has to supply fst, of type A, together with a snd, of type B
  constructor _,_
  field
    fst : A
    snd : B

-- this exposes fst and snd as functions
-- fst : A × B → A
-- snd : A × B → B
open _×_

data _⊎_ (A B : Set) : Set where -- AKA logical or, sum type, disjoint union
  -- a type packing up either an A or a B
  -- A and B are type parameters
  -- inl and inr are constructors,
  -- constructors can take arguments: inl takes an A, inr takes a B
  -- one can make something of type A ⊎ B by saying inl and supplying an A, or by saying inr and supplying a B
  inl : A → A ⊎ B
  inr : B → A ⊎ B


--------
-- Some simple proofs!
--------

-- a polymorphic function parametrised over A and B
-- brackets make an argument implicit:
-- you don't *have* to provide it, although you can if you want
-- you don't *have* to list it as an argument in the function definition, although you can if you want
-- functions as (constructive) implication: a proof of A × B implies a proof of A
get-fst : {A : Set} {B : Set} → A × B → A
get-fst x = {!!}

-- Agda is an *interactive* proof assistant
-- ctrl+c is the prefix that we use to communicate with Agda
-- ctrl+c ctrl+l reload the file
-- ctrl+c ctrl+, shows the goal and the context
-- ctrl+c ctrl+c pattern matches against a given arguments
-- ctrl+c ctrl+. shows the goal, the context, and what we have so far
-- ctrl+c ctrl+a try to automatically fulfill the goal
-- key bindings: https://agda.readthedocs.io/en/v2.6.1.3/getting-started/quick-guide.html
get-snd : ∀ {A B} → A × B → B
get-snd x = {!x!}

curry : {A B C : Set} → (A → B → C) → (A × B → C)
curry f (a , b) = f a b

uncurry : {A B C : Set} → (A × B → C) → (A → B → C)
uncurry f a b = f (a , b)

-- ctrl+c ctrl+r refines the goal: it will ask Agda to insert the first constructor we need
×-comm : ∀ {A B} → A × B → B × A
×-comm = {!!}

-- ctrl+c ctrl+a tries to automatically solve the goal
×-assoc : ∀ {A B C} → (A × B) × C → A × (B × C)
×-assoc = {!!}

-- pattern matching has to be exhaustive: all cases must be addressed
⊎-comm : ∀ {A B} → A ⊎ B → B ⊎ A
⊎-comm = {!!}

⊎-assoc : ∀ {A B C} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc = {!!}

-- if there are no cases to be addressed, there is nothing we have to don't
-- if you believe Zero exist, you believe anything
-- in most programming languages you deal with impossibilities by raise Exception("This should never happen.")
-- in Agda we can make the compiler understand the impossibility of certain situations
absurd : {A : Set} → ⊥ → A
absurd a = {!!}

-- negation: we show something is impossible by using it to construct Zero (which we know to be impossible)
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- one can write two possible programs here
×-⇒-⊎ : ∀ {A B} → A × B → A ⊎ B
×-⇒-⊎ = {!!}

-- this is a little more involved
-- higher order function: we take a function as an argument
⊎-⇏-× : ¬ (∀ {A B} → A ⊎ B → A × B)
⊎-⇏-× f = {!fst!}


--------
-- Inductive data types
--------


data ℕ : Set where
  -- the type of unary natural numbers
  -- the zero constructor takes no arguments
  -- the suc constructor takes one argument: a natural number that we previously made
  -- zero is the base case
  -- suc is the inductive case
  -- we represent natural numbers by using ticks: ||| ≈ 3
  -- zero: no ticks
  -- suc: one more tick
  -- suc (suc (suc zero)) ≈ ||| ≈ 3
  zero : ℕ
  suc  : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

-- compiler pragmas are introduced with an opening {-# and a closing #-}
-- here we use it to tell Agda to use ℕ as the builtin type for natural numbers
-- this allows us to say 3 instead of suc (suc (suc zero))
{-# BUILTIN NATURAL ℕ #-}
three' : ℕ
three' = 3

-- we can define addition of natural numbers by structural recursion
infixl 20 _+_
_+_ : ℕ → ℕ → ℕ
x + y = {!!}

-- recursion must occur on structurally smaller arguments
-- otherwise the computation might never end
-- in Agda *all computations must end*
-- we can tell Agda to ignore non-termination with this pragma
{-# TERMINATING #-}
non-terminating : ℕ → ℕ
non-terminating n = non-terminating n

-- if things were to not terminate we could create falsehood out of thin air
{-# TERMINATING #-}
loop : ⊥
loop = loop

-- let's now use structural recursion to define multiplication
_*_ : ℕ → ℕ → ℕ
x * y = {!!}

-- introduce modules
module Lists where
  -- introduce precedence
  -- defaults to 20
  -- the higher the precedence, the tighter it binds
  infixr 15 _∷_ _++_

  data List (A : Set) : Set where
    -- lists are another inductive data type
    -- like natural numbers, but the successor case contains an A
    [] : List A
    _∷_ : A → List A → List A

  -- list concatenation by structural recursion
  _++_ : ∀ {A} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map : ∀ {A B} → (A → B) → List A → List B
  map = {!!}

  foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)

--------
-- Dependent Types
--------

-- A predicate P on a type A is a function from elements of A into types
Pred : Set → Set₁
Pred A = A → Set

Even : Pred ℕ
Even x = {!!}

-- Here Even n computes as we expose the constructors of n
half : (n : ℕ) → Even n → ℕ
half n n-even = {!!}

-- Introduce variables
variable
  ℓ : Level
  A B C : Set ℓ
  n m : ℕ

-- Introduce type indices
data EvenData : Pred ℕ where
  zero : EvenData zero
  2+_  : EvenData n → EvenData (suc (suc n))

-- Here EvenData n needs to be taken appart explicitly
-- It leaves a trace of *why* n is even
half-data : (n : ℕ) → EvenData n → ℕ
half-data n n-even = {!!}

--------
-- Example of common uses of dependent types
--------

data Fin : ℕ → Set where -- a type with n distinct elements
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

Fin0 : Fin zero → ⊥
Fin0 x = {!!}

module Vecs where
  data Vec (A : Set) : ℕ → Set where -- vectors: lists of a given length
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  _++_ : Vec A n → Vec A m → Vec A (n + m)
  xs ++ ys = {!!}

  map : ∀ {A B} → (A → B) → Vec A n → Vec B n
  map = {!!}

  _!_ : Vec A n → Fin n → A
  xs ! i = {!!}

data _≤_ : ℕ → ℕ → Set where
  z≤n :         zero  ≤ n
  s≤s : n ≤ m → suc n ≤ suc m

-----------
-- Propositional Equality
-----------

data _≡_ : A → A → Set where
  refl : {x : A} → x ≡ x

-- Introduce presendence
infix 10 _≡_

-- Introduce definitional equality
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = {!!}

sym : {x y : A} → x ≡ y → y ≡ x
sym p = {!!}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}

cong : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!!}

cong₂ : {x y : A} {w z : B} (f : A → B → C) → x ≡ y → w ≡ z → f x w ≡ f y z
cong₂ f refl refl = refl

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

+-idˡ : ∀ x → (zero + x) ≡ x
+-idˡ x = {!!}

-- Introduce proof by induction
+-idʳ : ∀ x → (x + zero) ≡ x
+-idʳ x = {!!}

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc x y z = {!!}

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc x y = {!!}

-- Introduce underscores on the RHS
+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = {!!}
+-comm x (suc y) = {!!}

-- Introduce equational reasoning
infix  3 _∎
infixr 2 step-≡
infix  1 begin_

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl


+-comm′ : ∀ x y → x + y ≡ y + x
+-comm′ x zero = {!!}
+-comm′ x (suc y) = begin
  (x + suc y)  ≡⟨ {!!} ⟩
  suc (x + y)  ≡⟨ {!!} ⟩
  suc (y + x)  ∎

-----------
-- Decidability
-----------

module Dec where
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

  open Lists using (List; []; _∷_)

  ∷-injective : {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-injective refl = refl , refl

  List-≟ : (_A-≟_ : (x y : A) → Dec (x ≡ y)) → (xs ys : List A) → Dec (xs ≡ ys)
  List-≟ _A-≟_ [] [] = yes refl
  List-≟ _A-≟_ [] (y ∷ ys) = no λ ()
  List-≟ _A-≟_ (x ∷ xs) [] = no λ ()
  List-≟ _A-≟_ (x ∷ xs) (y ∷ ys) = map (yes ∘ curry (cong₂ _∷_)) (no ∘ (λ neq → neq ∘ ∷-injective)) (x A-≟ y ×-dec List-≟ _A-≟_ xs ys)

BiPred : Set → Set₁
BiPred A = A → A → Set

module _ {A} (_LT_ : BiPred A) (_EQ_ : BiPred A) where
  private
    variable
      x y : A

  data Trichotomous : A → A → Set where
    lt : x LT y → Trichotomous x y
    eq : x EQ y → Trichotomous x y
    gt : y LT x → Trichotomous x y

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

suc-trichotomous : {n m : ℕ} → Trichotomous _<_ _≡_ n m → Trichotomous _<_ _≡_ (suc n) (suc m)
suc-trichotomous (lt x) = lt (s≤s x)
suc-trichotomous (eq x) = eq (cong suc x)
suc-trichotomous (gt x) = gt (s≤s x)

ℕ-trichotomous : (n m : ℕ) → Trichotomous _<_ _≡_ n m
ℕ-trichotomous zero zero = eq refl
ℕ-trichotomous zero (suc m) = lt (s≤s z≤n)
ℕ-trichotomous (suc n) zero = gt (s≤s z≤n)
ℕ-trichotomous (suc n) (suc m) = suc-trichotomous (ℕ-trichotomous n m)

-----------
-- Pi and Sigma types
-----------

module Products where
  Π : (A : Set) → (A → Set) → Set
  Π A P = (x : A) → P x

  record Σ (A : Set) (B : Pred A) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  infix 2 Σ-syntax
  Σ-syntax : (A : Set) → (A → Set) → Set
  Σ-syntax = Σ
  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  map : {P : Pred A} {Q : Pred B} → (f : A → B) → (∀ {x} → P x → Q (f x)) → Σ A P → Σ B Q
  map f g (x , y) = (f x , g y)

-- Introduce anonymous modules
module _ where
  -- Introduce module opening
  open Products using (Π; Σ; Σ-syntax; _,_)
  open Vecs using (Vec; []; _∷_)
  open Dec using (Dec)

  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ x y = {!!}

  take : Vec A m → n ≤ m → Vec A n
  take xs lte = {!!}

  to-ℕ : Fin n → ℕ
  to-ℕ zero = zero
  to-ℕ (suc x) = suc (to-ℕ x)

  -- Proof combining sigma types and equality
  ≤-to-Fin : n ≤ m → Σ[ x ∈ Fin (suc m) ] to-ℕ x ≡ n
  ≤-to-Fin z≤n = {!!}
  ≤-to-Fin (s≤s lte) = {!!}

  module _ {A : Set} {P : A → Set} where

    -- These can be proven regardless of A

    ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬_ ∘ P)
    ¬∃⇒∀¬ = {!!}

    ∃¬⇒¬∀ : Σ A (¬_ ∘ P) → ¬ Π A P
    ∃¬⇒¬∀ = {!!}

    ∀¬⇒¬∃ : Π A (¬_ ∘ P) → ¬ Σ A P
    ∀¬⇒¬∃ = {!!}

    -- Works in classical, not in constructive mathematics
    -- Unless A is discrete, inhabited, and finite, and P is decidable
    postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬_ ∘ P)

-----------
-- Interfaces
-----------

module Monoids where
  open Lists using (List; []; _∷_; _++_)
  open Vecs using (Vec; []; _∷_; _!_)

  -- We define what it is to be a monoid
  record Monoid (C : Set) : Set where
    constructor MkMonoid
    field
      ε   : C
      _∙_ : C → C → C
      -- Including the algebraic laws
      idˡ : (x : C) → ε ∙ x ≡ x
      idʳ : (x : C) → x ∙ ε ≡ x
      assoc : (x y z : C) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  infixl 20 _‵∙_
  data Expr : ℕ → Set where
    ‵_ : Fin n → Expr n
    ‵ε : Expr n
    _‵∙_ : Expr n → Expr n → Expr n

  infix 10 _‵≡_
  record Eqn (n : ℕ) : Set where
    constructor _‵≡_
    field
      lhs : Expr n
      rhs : Expr n

  NormalForm : ℕ → Set
  NormalForm n = List (Fin n)

  normalise : Expr n → NormalForm n
  normalise (‵ x) = x ∷ []
  normalise ‵ε = []
  normalise (xs ‵∙ ys) = normalise xs ++ normalise ys

  ++-assoc : (xs ys zs : List C) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  module Eval (M : Monoid C) where
    open Monoid M

    Env : ℕ → Set
    Env n = Vec C n

    ⟦_⟧ : Expr n → Env n → C
    ⟦ ‵ x ⟧ Γ = Γ ! x
    ⟦ ‵ε ⟧ Γ = ε
    ⟦ x ‵∙ y ⟧ Γ = ⟦ x ⟧ Γ ∙ ⟦ y ⟧ Γ

    ⟦_⟧⇓ : NormalForm n → Env n → C
    ⟦ [] ⟧⇓ Γ = ε
    ⟦ x ∷ xs ⟧⇓ Γ = (Γ ! x) ∙ ⟦ xs ⟧⇓ Γ

    ++-homo : ∀ Γ (xs ys : NormalForm n) → ⟦ xs ++ ys ⟧⇓ Γ ≡ ⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ
    ++-homo Γ [] ys = sym (idˡ _)
    ++-homo Γ (x ∷ xs) ys = begin
      (Γ ! x) ∙ ⟦ xs ++ ys ⟧⇓ Γ
        ≡⟨ cong (_ ∙_) (++-homo Γ xs ys) ⟩
      (Γ ! x) ∙ (⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ)
        ≡⟨ sym (assoc _ _ _) ⟩
      ((Γ ! x) ∙ ⟦ xs ⟧⇓ Γ) ∙ ⟦ ys ⟧⇓ Γ
        ∎

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

    Solution : Eqn n → Set
    Solution (lhs ‵≡ rhs) =
      Dec.map
        (λ _ → ∀ (Γ : Env _) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)
        (λ _ → ⊤)
        (Dec.List-≟ Dec._Fin-≟_ (normalise lhs) (normalise rhs))

    solve : (eqn : Eqn n) → Solution eqn
    solve (lhs ‵≡ rhs) with Dec.List-≟ Dec._Fin-≟_ (normalise lhs) (normalise rhs)
    solve (lhs ‵≡ rhs) | Dec.no _ = tt
    solve (lhs ‵≡ rhs) | Dec.yes lhs⇓≡rhs⇓ = λ Γ → begin
      ⟦ lhs ⟧ Γ
        ≡⟨ sym (correct Γ lhs) ⟩
      ⟦ normalise lhs ⟧⇓ Γ
        ≡⟨ cong (λ ● → ⟦ ● ⟧⇓ Γ) lhs⇓≡rhs⇓ ⟩
      ⟦ normalise rhs ⟧⇓ Γ
        ≡⟨ correct Γ rhs ⟩
      ⟦ rhs ⟧ Γ
        ∎

  NAT-MONOID : Monoid ℕ
  Monoid.ε NAT-MONOID = zero
  Monoid._∙_ NAT-MONOID = _+_
  Monoid.idˡ NAT-MONOID = +-idˡ
  Monoid.idʳ NAT-MONOID = +-idʳ
  Monoid.assoc NAT-MONOID = +-assoc

  eqn₁-auto : (x y z : ℕ) → (0 + x) + y + (y + z) ≡ x + (0 + y + 0) + (z + 0)
  eqn₁-auto x y z =
    let
      ‵x = zero
      ‵y = suc zero
      ‵z = suc (suc zero)
    in
      Eval.solve NAT-MONOID ((‵ε ‵∙ (‵ ‵x)) ‵∙ (‵ ‵y) ‵∙ ((‵ ‵y) ‵∙ (‵ ‵z)) ‵≡ ((‵ ‵x) ‵∙ (‵ε ‵∙ (‵ ‵y) ‵∙ ‵ε) ‵∙ ({!‵ ‵z!} ‵∙ ‵ε)))
