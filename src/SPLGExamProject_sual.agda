module SPLGExamProject_sual where

open import Prelude
open import Lecture3Delivery

open Lists
open Nats
open Eq
open Sum
open LessThan

min : (n m : Nat) → Either (n <= m) (m <= n)
min zero m = left zero<=
min (suc n) zero = right zero<=
min (suc n) (suc m) with min n m
min (suc n) (suc m) | left x = left (suc<= x)
min (suc n) (suc m) | right x = right (suc<= x)

insert : Nat → List Nat → List Nat
insert x [] = x :: []
insert x (y :: xs) with min x y
insert x (y :: xs) | left  x<=y = x :: y :: xs
insert x (y :: xs) | right y<=x = y :: insert x xs

insertionSort : List Nat → List Nat
insertionSort [] = []
insertionSort (x :: xs) = insert x (insertionSort xs)

open BagEquality
open Isomorphisms
open IsomorphismSyntax

-- Lemma 1: If P holds for an element in insert x xs, then P either holds for x or for xs.
isInInsert : ∀ {x xs P} → Any P (insert x xs) <-> Either (P x) (Any P xs)
-- Induction on the base list.
-- Base case:
-- Any P (insert x []) <-> Either (P x) (Any P [])
-- Any P (insert x []) simplifies to: Any P (x :: [])
-- which simplifies to Either (P x) (Any P [])
-- Therefore this is trivial.
isInInsert {x} {[]} {P} = iso-refl
-- Step case: 
-- Any P (insert x (y :: xs)) <-> Either (P x) (Any P (y :: xs)
-- Induction hypothesis: Any P (insert x xs) <-> Either (P x) (Any P xs)
-- Case analysis on the relationship between x and y
isInInsert {x} {y :: xs} {P} with min x y 
-- If x is less than or equal to y the case is trivial.
-- In this case insert simplifies to x :: y :: xs
-- which is the cons case.
-- Therefore we know the isomorphism to hold by the definition of Any
isInInsert {x} {y :: xs} {P} | left x<=y  = iso-refl
-- If y is less than or equal to x this simplifies to y :: (insert x xs).
-- This means that we have that P either holds for y, or for an element in insert x xs
isInInsert {x} {y :: xs} {P} | right y<=x = Either (P y)                (Any P (insert x xs))     <->[ Either-cong iso-refl (isInInsert) ]
-- Here I use the induction hypothesis (isInInsert P) from earlier.
-- I use Either-cong (from Lecture 3) to only apply the IH to the right branch. 
                                            Either (P y)                (Either (P x) (Any P xs)) <->[ iso-sym Either-assoc ] 
-- From here it is just simple rewrites on Either using different lemma from Lecture 3.
                                            Either (Either (P y) (P x)) (Any P xs)                <->[ Either-cong Either-comm iso-refl ]
                                            Either (Either (P x) (P y)) (Any P xs)                <->[ Either-assoc ] 
                                            Either (P x)                (Either (P y) (Any P xs)) QED

-- Theorem 1: Given a list of natural numbers, the sorted list is bag equal to the original list. 
insSortKeepsBagEq : (l : List Nat) → insertionSort l =bag l 
-- Induction on the list
-- Base case:
-- Any P insertionSort [] <-> Any P []
-- insertionSort [] simplifies to [] making this case trivial.
insSortKeepsBagEq [] = =bag-refl
-- Step case:
-- Any P insertionSort (x :: xs) <-> Any P (x :: xs)
-- Induction hypothesis: Any P (insertionSort xs) <-> Any P xs 
insSortKeepsBagEq (x :: xs) = λ z → Any (_==_ z) (insert x (insertionSort xs)) <->[ isInInsert ]
-- Use Lemma 1 to rewrite
                                    Either (z == x) (Any (_==_ z) (insertionSort xs)) <->[ Either-cong iso-refl (insSortKeepsBagEq xs z) ]
-- Use induction hypothesis
                                    Either (z == x) (Any (_==_ z) xs) QED

open Sigma

-- Theorem 2: Given a list of natural numbers, returns a dependent pair where the first element is the sorted list, 
-- and the second element is a proof that the first element is bag equal to the input list.
insSortWithProof : ∀ (l : List Nat) → (List Nat ** λ sl → sl =bag l)
-- This is straightforward as it is just using our previous proof.
insSortWithProof l = insertionSort l , insSortKeepsBagEq l
