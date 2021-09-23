module Monday where


-- two dashes to comment out the rest of the line
{-
  opening {- and closing -} for a
  multi-line comment
-}


data Zero : Set where
  -- : declares the type of something
  -- Zero : Set means Zero is a Type (Set = Type, for historical reasons)
  -- data creates a data type
  -- we list all of its constructors, all the ways in which we can make a Zero
  -- no constructors: no way of making a Zero
  -- the impossible type

record One : Set where
  -- record creates a record type
  -- records have a single constructor
  -- to create a record you must populate all of its fields
  -- One has no fields: it's trivial to make one
  -- zero bits worth of information
  constructor <>

data Two : Set where
  -- booleans: two ways of making a Two
  -- one bit worth of information
  true : Two
  false : Two

--------
-- Simple composite types
--------

record _×_ (A : Set) (B : Set) : Set where
  -- a type packing up an A and a B
  -- A and B are type parameters
  -- fst and snd are fields
  -- each fields has a type, the type of fst is A, the type of snd is B
  -- to make something of type A × B, one has to supply fst, of type A, together with a snd, of type B
  -- logical and
  constructor _,_
  field
    fst : A
    snd : B

-- this exposes fst and snd as functions
-- fst : A × B → A
-- snd : A × B → B
open _×_

data _⊎_ (A B : Set) : Set where
  -- a type packing up either an A or a B
  -- A and B are type parameters
  -- inl and inr are constructors,
  -- constructors can take arguments: inl takes an A, inr takes a B
  -- one can make something of type A ⊎ B by saying inl and supplying an A, or by saying inr and supplying a B
  -- logical or
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
get-fst (fst , snd) = fst

-- Agda is an *interactive* proof assistant
-- ctrl+c is the prefix that we use to communicate with Agda
-- ctrl+c ctrl+, shows the goal and the context
-- ctrl+c ctrl+c pattern matches against a given arguments
-- ctrl+c ctrl+. shows the goal, the context, and what we have so far
-- key bindings: https://agda.readthedocs.io/en/v2.6.1.3/getting-started/quick-guide.html
get-snd : ∀ {A B} → A × B → B
get-snd x = {!x!}

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
absurd : {A : Set} → Zero → A
absurd a = {!!}

-- one can write two possible programs here
×-⇒-⊎ : ∀ {A B} → A × B → A ⊎ B
×-⇒-⊎ = {!!}

-- this is a little more involved
-- higher order function: we take a function as an argument
-- we show that the existence of such function is impossible by using it to construct Zero (the canonical impossible)
⊎-⇏-× : (∀ {A B} → A ⊎ B → A × B) → Zero
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
loop : Zero
loop = loop

-- let's now use structural recursion to define multiplication
_*_ : ℕ → ℕ → ℕ
x * y = {!!}

data List (A : Set) : Set where
  -- lists are another inductive data type
  -- like natural numbers, but the successor case contains an A
  [] : List A
  _∷_ : A → List A → List A

-- list concatenation by structural recursion
_++_ : ∀ {A} → List A → List A → List A
xs ++ ys = {!!}


--------
-- Dependent Types
--------

Even : ℕ → Set
Even x = {!!}

half : (n : ℕ) → Even n → ℕ
half n n-even = {!!}

-- Introduce variables
variable
  A B : Set
  n : ℕ

-- Introduce type indices
data EvenData : ℕ → Set where
  zero : EvenData zero
  2+_  : EvenData n → EvenData (suc (suc n))


-- Introduce propositional equality
data _≡_ : A → A → Set where
  refl : {x : A} → x ≡ x

-- Introduce presendence
infix 5 _≡_

-- Introduce judgmental equality
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = {!!}

sym : {x y : A} → x ≡ y → y ≡ x
sym p = {!!}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}

cong : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!!}

+-idˡ : ∀ x → (zero + x) ≡ x
+-idˡ x = {!!}

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
infixr 2 _≡⟨⟩_ step-≡ step-≡˘
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


-- Things to remember to say

-- Introduce : notation
-- Tokenising by spacing
-- Introduce unicode
-- Introduce misfix notation
