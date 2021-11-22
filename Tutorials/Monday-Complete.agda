{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (Level)
module Tutorials.Monday-Complete where


-- Two dashes to comment out the rest of the line
{-
  Opening {-
  and closing -}
  for a multi-line comment
-}

-- In Agda all the tokens are tokenised using whitespace (with the exception of parentheses and some other symbols)
-- Agda offers unicode support
-- We can input unicode using the backslash \ and (most of the time) typing what one would type in LaTeX
-- If in emacs, we can put the cursor over a characted and use M-x describe-char to see how that character is inputted
-- ⊥ is written using \bot
data ⊥ : Set where
  -- AKA the empty set, bottom, falsehood, the absurd type, the empty type, the initial object
  -- ⊥ : Set means ⊥ is a Type (Set = Type, for historical reasons)
  -- The data keyword creates a data type where we list all the constructors of the types
  -- ⊥ has no constructors: there is no way of making something of type ⊥

record ⊤ : Set where
  -- AKA the singleton set, top, truth, the trivial type, the unit type, the terminal object
  -- The record keyword creates a record type
  -- Records have a single constructor
  -- To create a record you must populate all of its fields
  -- ⊤ has no fields: it is trivial to make one, and contains no information
  constructor tt

data Bool : Set where
  -- Bool has two constructors: one bit worth of information
  true : Bool
  false : Bool

--------
-- Simple composite types
--------

module Simple where
  record _×_ (A : Set) (B : Set) : Set where
    -- AKA logical and, product type

    -- Agda offers support for mixfix notation
    -- We use the underscores to specify where the arguments goal
    -- In this case the arguments are the type parameters A and B, so we can write A × B

    -- A × B models a type packing up *both* an A *and* a B
    -- A and B are type parameters, both of type Set, i.e. types
    -- A × B itself is of type Set, i.e. a type
    -- We use the single record constructor _,_ to make something of type A × B
    -- The constructor _,_ takes two parameters: the fields fst and snd, of type A and B, respectively
    -- If we have a of type A and b of type B, then (a , b) is of type A × B
    constructor _,_
    field
      fst : A
      snd : B

  -- Agda has a very expressive module system (more on modules later)
  -- Every record has a module automatically attached to it
  -- Opening a record exposes its constructor and it fields
  -- The fields are projection functions out of the record
  -- In the case of _×_, it exposes
  -- fst : A × B → A
  -- snd : A × B → B
  open _×_

  data _⊎_ (A B : Set) : Set where
    -- AKA logical or, sum type, disjoint union
    -- A ⊎ B models a type packing *either* an A *or* a B
    -- A and B are type parameters, both of type Set, i.e. types
    -- A ⊎ B itself is of type Set, i.e. a type
    -- A ⊎ B has two constructors: inl and inr
    -- The constructor inl takes something of type A as an argument and returns something of type A ⊎ B
    -- The constructor inr takes something of type B as an argument and returns something of type A ⊎ B
    -- We can make something of type A ⊎ B either by using inl and supplying an A, or by using inr and supplying a B
    inl : A → A ⊎ B
    inr : B → A ⊎ B


  --------
  -- Some simple proofs!
  --------

  -- In constructive mathematics logical implication is modelled as function types
  -- An object of type A → B shows that assuming an object of type A, we can construct an object of type B
  -- Below we want to show that assuming an object of type A × B, we can construct an object of type A
  -- We want to show that this is the case regardless of what A and B actually are
  -- We do this using a polymorphic function that is parametrised over A and B, both of type Set
  -- We use curly braces {} to make these function parameters implicit
  -- When we call this function we won't have to supply the arguments A and B unless we want to
  -- When we define this function we won't have to accept A and B as arguments unless we want to
  -- The first line below gives the type of the function get-fst
  -- The second line gives its definition
  get-fst : {A : Set} {B : Set} → A × B → A
  get-fst (x , y) = x

  -- Agda is an *interactive* proof assistant
  -- We don't provide our proofs/programs all at once: we develop them iteratively
  -- We write ? where we don't yet have a program to provide, and we reload the file
  -- What we get back is a hole where we can place the cursor and have a conversation with Agda
  -- ctrl+c is the prefix that we use to communicate with Agda
  -- ctrl+c ctrl+l     reload the file
  -- ctrl+c ctrl+,     shows the goal and the context
  -- ctrl+c ctrl+.     shows the goal, the context, and what we have so far
  -- ctrl+c ctrl+c     pattern matches against a given arguments
  -- ctrl+c ctrl+space fill in hole
  -- ctrl+c ctrl+r     refines the goal: it will ask Agda to insert the first constructor we need
  -- ctrl+c ctrl+a     try to automatically fulfill the goal
  -- key bindings: https://agda.readthedocs.io/en/v2.6.1.3/getting-started/quick-guide.html
  get-snd : ∀ {A B} → A × B → B
  get-snd (x , y) = y

  -- The variable keyword enables us to declare convention for notation
  -- Unless said otherwise, whenever we refer to A, B or C and these are not bound, we will refer to objects of type Set
  variable
    ℓ : Level
    A B C : Set ℓ

  -- Notice how we don't have to declare A, B and C anymore
  curry : (A → B → C) → (A × B → C)
  curry f (a , b) = f a b

  uncurry : (A × B → C) → (A → B → C)
  uncurry f a b = f (a , b)

  ×-comm : A × B → B × A
  ×-comm (a , b) = b , a

  ×-assoc : (A × B) × C → A × (B × C)
  ×-assoc ((a , b) , c) = a , (b , c)

  -- Pattern matching has to be exhaustive: all cases must be addressed
  ⊎-comm : A ⊎ B → B ⊎ A
  ⊎-comm (inl x) = inr x
  ⊎-comm (inr x) = inl x

  ⊎-assoc : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  ⊎-assoc (inl (inl x)) = inl x
  ⊎-assoc (inl (inr x)) = inr (inl x)
  ⊎-assoc (inr x) = inr (inr x)

  -- If there are no cases to be addressed there is nothing for us left to do
  -- If you believe ⊥ exist you believe anything
  absurd : ⊥ → A
  absurd ()

  -- In constructive mathematics all proofs are constructions
  -- How do we show that an object of type A cannot possibly be constructed, while using a construction to show so?
  -- We take the cannonically impossible-to-construct object ⊥, and show that if we were to assume the existence of A, we could use it to construct ⊥
  ¬_ : Set ℓ → Set ℓ
  ¬ A = A → ⊥

  -- In classical logic double negation can be eliminated: ¬ ¬ A ⇒ A
  -- That is however not the case in constructive mathematics:
  -- The proof ¬ ¬ A is a function that takes (A → ⊥) into ⊥, and offers no witness for A
  -- The opposite direction is however constructive:
  ⇒¬¬ : A → ¬ ¬ A
  ⇒¬¬ a f = f a

  -- Moreover, double negation can be eliminated from non-witnesses
  ¬¬¬⇒¬ : ¬ ¬ ¬ A → ¬ A
  ¬¬¬⇒¬ f a = f (⇒¬¬ a)

  -- Here we have a choice of two programs to write
  ×-⇒-⊎₁ : A × B → A ⊎ B
  ×-⇒-⊎₁ (a , b) = inl a

  ×-⇒-⊎₂ : A × B → A ⊎ B
  ×-⇒-⊎₂ (a , b) = inr b

  -- A little more involved
  -- Show that the implication (A ⊎ B → A × B) is not always true for all A and Bs
  ⊎-⇏-× : ¬ (∀ {A B} → A ⊎ B → A × B)
  ⊎-⇏-× f = snd (f {A = ⊤} {B = ⊥} (inl tt))

-- -> \to → \-> → \forall ∀ \ell ℓ
variable
  ℓ : Level
  A B C : Set ℓ

--------
-- Inductive data types
--------
-- \bN ℕ
data ℕ : Set where
  -- The type of unary natural numbers
  -- The zero constructor takes no arguments; the base case
  -- The suc constructor takes one argument: an existing natural number; the inductive case
  -- We represent natural numbers by using ticks: ||| ≈ 3
  -- zero: no ticks
  -- suc: one more tick
  -- suc (suc (suc zero)) ≈ ||| ≈ 3
  zero : ℕ
  suc  : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

-- Compiler pragmas allow us to give instructions to Agda
-- They are introduced with an opening {-# and a closing #-}
-- Here we the pragma BUILTIN to tell Agda to use ℕ as the builtin type for natural numbers
-- This allows us to say 3 instead of suc (suc (suc zero))
{-# BUILTIN NATURAL ℕ #-}
three' : ℕ
three' = 3

-- Whenever we say n or m and they haven't been bound, they refer to natural numbers
variable
  n m l : ℕ

-- Brief interlude: we declare the fixity of certain functions
-- By default, all definitions have precedence 20
-- The higher the precedence, the tighter they bind
-- Here we also declare that _+_ is left associative, i.e. 1 + 2 + 3 is parsed as (1 + 2) + 3
infixl 20 _+_
-- x + y + z ≡ (x + y) + z

-- Define addition of natural numbers by structural recursion
_+_ : ℕ → ℕ → ℕ
zero + y = y
(suc x) + y = suc (x + y)

-- In functions recursion must always occur on structurally smaller values (otherwise the computation might never terminate)
-- In Agda *all computations must terminate*
-- We can tell Agda to ignore non-termination with this pragma
{-# TERMINATING #-}
non-terminating : ℕ → ℕ
non-terminating n = non-terminating n

-- However, doing so would allow us to define elements of the type ⊥
-- This is not considered safe: running Agda with the --safe option will make type-checking fail
{-# TERMINATING #-}
loop : ⊥
loop = loop

-- Use structural recursion to define multiplication
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

-- The module keyword allows us to define modules (namespaces)
module List where
  infixr 15 _∷_ _++_
  data List (A : Set) : Set where
    -- Lists are another example of inductive types
    -- The type parameter A is the type of every element in the list
    -- They are like natural numbers, but the successor case contains an A
    []  : List A
    _∷_ : A → List A → List A

  example₁ : List Bool
  example₁ = true ∷ false ∷ []  -- [true, false]

  -- List concatenation by structural recursion
  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- Apply a function (A → B) to every element of a list
  map : (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- A base case B and an inductive case A → B → B is all we need to take a List A and make a B
  foldr : (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)

--------
-- Dependent Types
--------

-- Dependent types are types that depend on values, objects of another type
-- Dependent types allow us to model predicates on types
-- A predicate P on a type A is a function taking elements of A into types
Pred : Set → Set₁
Pred A = A → Set

-- Let us define a predicate on ℕ that models the even numbers
-- Even numbers are taken to the type ⊤, which is trivial to satisfy
-- Odd numbers are taken to the type ⊥, which is impossible to satisfy
Even : Pred ℕ
Even zero = ⊤
Even (suc zero) = ⊥
Even (suc (suc x)) = Even x

-- We can now use Even as a precondition on a previous arguments
-- Here we bind the first argument of type ℕ to the name n
-- We then use n as an argument to the type Even
-- As we expose the constructors of n, Even will compute
half : (n : ℕ) → Even n → ℕ
half zero n-even = zero
half (suc (suc n)) n-even = suc (half n n-even)

-- There is an alternative way of definiting dependent types
-- EvenData is a data type indexed by elements of the type ℕ
-- That is, for every (n : ℕ), EvenData n is a type
-- The constructor zero constructs an element of the type EvenData zero
-- The constructor 2+_ takes an element of the type EvenData n and constructs one of type EvenData (suc (suc n))
-- Note that there is no constructors that constructs elements of the type Evendata (suc zero)
data EvenData : ℕ → Set where -- Pred ℕ
  zero : EvenData zero
  2+_  : EvenData n → EvenData (suc (suc n))

-- We can use EvenData as a precondition too
-- The difference is that while Even n computes automatically, we have to take EvenData n appart by pattern matching
-- It leaves a trace of *why* n is even
half-data : (n : ℕ) → EvenData n → ℕ
half-data zero zero = zero
half-data (suc (suc n)) (2+ n-even) = suc (half-data n n-even)

-- Function composition: (f ∘ g) composes two functions f and g
-- The result takes the input, feeds it through g, then feeds the result through f
infixr 20 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

--------
-- Example of common uses of dependent types
--------

module Fin where
  -- The type Fin n has n distinct inhabitants
  data Fin : ℕ → Set where
    zero : Fin (suc n)
    suc  : Fin n → Fin (suc n)

  -- Note that there is no constructor for Fin zero
  Fin0 : Fin zero → ⊥
  Fin0 ()

  -- We can erase the type level information to get a ℕ back
  to-ℕ : Fin n → ℕ
  to-ℕ zero = zero
  to-ℕ (suc x) = suc (to-ℕ x)

module Vec where
  open Fin

  -- Vectors are like lists, but they keep track of their length
  -- The type Vec A n is the type of lists of length n containing values of type A
  -- Notice that while A is a parameter (remains unchanged in all constructors), n is an index
  -- We can bind parameters to names (since they don't change) but we cannot bind indices
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  -- Now we can define concatenation, but giving more assurances about the resulting length
  _++_ : Vec A n → Vec A m → Vec A (n + m)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map : (A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  -- Given a vector and a fin, we can use the latter as a lookup index into the former
  -- Question: what happens if there vector is empty?
  _!_ : Vec A n → Fin n → A
  (x ∷ xs) ! zero = x
  (x ∷ xs) ! suc i = xs ! i

  -- A vector Vec A n is just the inductive form of a function Fin n → A
  tabulate : ∀ {n} → (Fin n → A) → Vec A n
  tabulate {n = zero}  f = []
  tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

  untabulate : Vec A n → (Fin n → A)
  untabulate [] ()
  untabulate (x ∷ xs) zero = x
  untabulate (x ∷ xs) (suc i) = untabulate xs i

-- Predicates need not be unary, they can be binary! (i.e. relations)
Rel : Set → Set₁
Rel A = A → A → Set

-- Question: how many proofs are there for any n ≤ m
data _≤_ : Rel ℕ where
  z≤n :         zero  ≤ n
  s≤s : n ≤ m → suc n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- _≤_ is reflexive and transitive
≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : n ≤ m → m ≤ l → n ≤ l
≤-trans z≤n b = z≤n
≤-trans (s≤s a) (s≤s b) = s≤s (≤-trans a b)

-----------
-- Propositional Equality
-----------

-- Things get interesting: we can use type indices to define propositional equality
-- For any (x y : A) the type x ≡ y is a proof showing that x and y are in fact definitionally equal
-- It has a single constructor refl which limits the ways of making something of type x ≡ y to those where x and y are in fact the same, i.e. x ≡ x
-- When we pattern match against something of type x ≡ y, the constructor refl will make x and y unify: Agda will internalise the equality
infix 10 _≡_
-- \== ≡
data _≡_ : A → A → Set where
  refl : {x : A} → x ≡ x

-- Definitional equality holds when the two sides compute to the same symbols
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = refl

-- Because of the way in which defined _+_, zero + x ≡ x holds definitionally (the first case in the definition)
+-idˡ : ∀ x → (zero + x) ≡ x
+-idˡ x = refl

-- We show that equality respects congruence
cong : {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!!}

-- However this does not hold definitionally
-- We need to use proof by induction
-- We miss some pieces to prove this
+-idʳ : ∀ x → (x + zero) ≡ x
+-idʳ zero = refl
+-idʳ (suc x) = {!!}

-- Propositional equality is reflexive by construction, here we show it is also symmetric and transitive
sym : {x y : A} → x ≡ y → y ≡ x
sym p = {!!}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}

-- A binary version that will come in use later on
cong₂ : {x y : A} {w z : B} (f : A → B → C) → x ≡ y → w ≡ z → f x w ≡ f y z
cong₂ f refl refl = refl

-- Leibniz equality, transport
subst : {x y : A} {P : Pred A} → x ≡ y → P x → P y
subst eq p = {!!}

-- Now we can start proving slightly more interesting things!
+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc x y z = {!!}

-- Introduce underscores on the RHS
+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = {!!}
+-comm x (suc y) = {!!}
  -- The keyword where allows us to introduce local definitions
  where
  +-suc : ∀ x y → x + suc y ≡ suc (x + y)
  +-suc x y = {!!}


-----------
-- Some tooling for equational reasoning
-----------

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

-- The equational resoning style allows us to explicitly write down the goals at each stage
-- This starts to look like what one would do on the whiteboard
+-comm′ : ∀ x y → x + y ≡ y + x
+-comm′ x zero = {!!}
+-comm′ x (suc y) = begin
  (x + suc y)  ≡⟨ {!!} ⟩
  suc (x + y)  ≡⟨ {!!} ⟩
  suc (y + x)  ∎
