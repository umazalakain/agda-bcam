{-# OPTIONS --allow-unsolved-metas --guardedness #-}

import Tutorials.Monday as Mon
import Tutorials.Tuesday as Tue
import Tutorials.Wednesday as Wed
open Mon using (⊤; tt; ℕ; zero; suc)
open Mon.Simple using (_⊎_; inl; inr)
open Tue.Product using (Σ; _,_; fst; snd; _×_)

module Tutorials.Thursday where

variable
  A B C S : Set

-- Things that we skipped so far
--------------------------------

module WithAbstraction where
  open Mon using (Bool; true; false; Pred; _≡_; refl; _+_; subst; +-comm)
  open Mon.List using (List; []; _∷_)

  -- With abstraction
  -- You can use "with abstraction" to pattern match on intermediary computations
  -- These can be nested, or executed simultaneously

  filter : (A → Bool) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) with f x
  filter f (x ∷ xs) | true = x ∷ filter f xs
  filter f (x ∷ xs) | false = filter f xs

  -- Alternative notation
  filter′ : (A → Bool) → List A → List A
  filter′ f [] = []
  filter′ f (x ∷ xs) with f x
  ...                | true = x ∷ filter′ f xs
  ...                | false = filter′ f xs


  -- The goal type and the type of the arguments are generalised over the value of the scrutinee
  thm : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  -- 1) Here (p : P (n + m)) and (eq : n + m ≡ m + n)
  -- thm n m p with +-comm n m
  -- thm n m p | eq = {!!}
  -- 2) Here (p : P x) and (eq : x ≡ m + n)
  -- thm n m p with n + m | +-comm n m
  -- thm n m p | x | eq = {!!}
  -- 3) Pattern matching we get (p : P (m + n)), the dot signifies that the argument is uniquely determined
  thm n m p with n + m | +-comm n m
  thm n m p | .(m + n) | refl = p

  -- This is such a common formula that there is special syntax for it
  thm′ : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm′ n m p rewrite +-comm n m = p

  -- We could use subst to be more explicit about *where* the rewrite happens
  thm′′ : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm′′ {P} n m p = subst {P = P} (+-comm n m) p


-- A little on coinductive types
--------------------------------

-- Stolen from https://github.com/pigworker/CS410-17/blob/master/lectures/Lec6Done.agda

ListT : Set → Set → Set
ListT X B = ⊤ ⊎ (X × B)

module List where
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  mkList : ListT A (List A) → List A
  mkList x = {!!}

  foldr : (ListT A B → B) → List A → B
  foldr alg xs = {!!}

  list-id : List A → List A
  list-id = {!!}

  incr : ListT A ℕ → ℕ
  incr x = {!!}

  length : List A → ℕ
  length = {!!}


module CoList where
  record CoList (A : Set) : Set where
    coinductive
    field
      next : ListT A (CoList A)

  open CoList

  [] : CoList A
  [] = {!!}

  _∷_ : A → CoList A → CoList A
  (x ∷ xs) = {!!}

  unfoldr : (S → ListT A S) → S → CoList A
  unfoldr coalg s = {!!}

  colist-id : CoList A → CoList A
  colist-id = {!!}

  repeat : A → CoList A
  repeat = {!!}

  take : ℕ → CoList A → List.List A
  take n xs = {!!}

module Stream where
  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A

  open Stream

  forever : A → Stream A
  forever x = {!!}

  unfold : (S → A × S) → S → Stream A
  unfold coalg s = {!!}



---------------------------------------------
-- If you are interested in more
-- Documentation for Agda: https://agda.readthedocs.io/en/v2.6.0.1/index.html
-- Programming Language Foundations in Agda: https://plfa.github.io/
-- Lots of other nice tutorials online
-- The standard library: https://agda.github.io/agda-stdlib/
