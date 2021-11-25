{-# OPTIONS --allow-unsolved-metas --guardedness #-}

import Tutorials.Monday-Complete
import Tutorials.Tuesday-Complete
import Tutorials.Wednesday-Complete
open Tutorials.Monday-Complete using (⊤; tt; ℕ; zero; suc)
open Tutorials.Monday-Complete.Simple using (_⊎_; inl; inr)
open Tutorials.Tuesday-Complete.Product using (Σ; _,_; fst; snd; _×_)

-- Stolen from https://github.com/pigworker/CS410-17/blob/master/lectures/Lec6Done.agda
module Tutorials.Thursday where

variable
  A B C S : Set

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


