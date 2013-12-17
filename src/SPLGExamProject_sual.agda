module SPLGExamProject_sual where

open import Prelude
open import Lecture3Delivery

open Lists
open Nats
open Eq
open Sum
open LessThan

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : Not A → Dec A

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

isInInsert : ∀ (x : Nat) (xs : List Nat) → (P : Nat -> Set) → Any P (insert x xs) <-> Either (P x) (Any P xs) -- x is in List after insert. The "insert" version of Any
isInInsert x [] P = Either (P x) Void QED -- Not sure how this works
isInInsert x (y :: xs) P with min x y -- Case analysis on the relation between x and y
isInInsert x (y :: xs) P | left x<=y = iso-refl
isInInsert x (y :: xs) P | right y<=x = Either (P y)                (Any P (insert x xs))     <->[ Either-cong iso-refl (isInInsert x xs P) ]
                                        Either (P y)                (Either (P x) (Any P xs)) <->[ iso-sym Either-assoc ] 
                                        Either (Either (P y) (P x)) (Any P xs)                <->[ Either-cong Either-comm iso-refl ]
                                        Either (Either (P x) (P y)) (Any P xs)                <->[ Either-assoc ] 
                                        Either (P x)                (Either (P y) (Any P xs)) QED

iso-insCons : ∀ {x xs} → (P : Nat -> Set) → (Any P (insert x xs)) <-> (Any P (x :: xs)) -- Containment is isomorphic for insert and cons 
iso-insCons {x} {xs} P = Any P (insert x xs) <->[ isInInsert x xs P ]
                         Either (P x) (Any P xs) QED 

insKeepsBagEq : ∀ {x} → (xs : List Nat) → (ys : List Nat) → (xs =bag ys) → (insert x xs) =bag (x :: ys) -- Inserting and consing has the same effect on bag equality
insKeepsBagEq {x} xs ys ok = λ z → Any    (_==_ z) (insert x xs)        <->[ iso-insCons (_==_ z) ] -- Use lemma about cons <-> insert
                                   Either (z == x) (Any (_==_ z) xs)    <->[ Either-cong iso-refl (ok z) ] -- Use lemma about cong for either
                                   Either (z == x) (Any (_==_ z) ys) QED

insSortKeepsBagEq : (l : List Nat) → insertionSort l =bag l -- Sorting a list keeps its bag equality
insSortKeepsBagEq [] = =bag-refl
insSortKeepsBagEq (x :: xs) = λ z → Any (_==_ z) (insert x (insertionSort xs)) <->[ insKeepsBagEq (insertionSort xs) xs (insSortKeepsBagEq xs) z ] -- Use induction hypothesis and lemma to prove
                                    Either (z == x) (Any (_==_ z) xs) QED

open Sigma

insSortWithProof : (l : List Nat) → (List Nat ** λ sl → sl =bag l)
insSortWithProof l = insertionSort l , insSortKeepsBagEq l
