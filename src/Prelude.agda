module Prelude where

id : {A : Set} -> A -> A
id x = x

compose : {A B C : Set} -> (A -> B) -> (B -> C) -> A -> C
compose f g = λ z → g (f z)

data Bool : Set where
  true false : Bool

module Nats where
  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  -- Magic to get literals
  {-# BUILTIN NATURAL Nat  #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  pred : Nat → Nat
  pred 0       = 0
  pred (suc n) = n

  private
    lit : Nat
    lit = 1337

  _+_ : Nat → Nat → Nat
  zero  + n = n
  suc m + n = suc (m + n)

module LessThan where
  open Nats

  data _<=_ : (m n : Nat) → Set where
    zero<= : {n : Nat} → zero <= n
    suc<=  : {m n : Nat} → m <= n → suc m <= suc n

  _<_ : Nat → Nat → Set
  m < n = suc m <= n

  max : Nat -> Nat -> Nat
  max zero zero = zero
  max zero (suc m) = suc m
  max (suc n) zero = suc n
  max (suc n) (suc m) = suc (max n m)

module Fin where
  open Nats

  -- `Fin n' represents a number less than n
  data Fin : Nat → Set where
    -- zero < suc n
    zero : {n : Nat} → Fin (suc n)
    -- i < n → suc i < suc n
    suc  : {n : Nat} → Fin n → Fin (suc n)

  toNat : {n : Nat} → Fin n → Nat
  toNat zero = zero
  toNat (suc i) = suc (toNat i)

-- Magic to get Agda happy about equality

postulate
  LEVEL : Set
  LSUC  : LEVEL → LEVEL
  LZERO : LEVEL
  LMAX  : LEVEL → LEVEL → LEVEL

{-# BUILTIN LEVEL LEVEL #-}
{-# BUILTIN LEVELSUC  LSUC  #-}
{-# BUILTIN LEVELZERO LZERO #-}
{-# BUILTIN LEVELMAX  LMAX   #-}

infix 4 _==_
data _==_ {a : LEVEL}{A : Set a}(x : A) : A → Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

module Eq where

  sym : {A : Set}{x y : A} → x == y → y == x
  sym refl = refl

  trans : {A : Set}{x y z : A} → x == y → y == z → x == z
  trans refl refl = refl

  cong : {A B : Set}{x y : A}(f : A → B) → x == y → f x == f y
  cong f refl = refl

  cong2 : {A B C : Set}{x y : A}{x' y' : B}(f : A → B → C) → x == y → x' == y' → f x x' == f y y'
  cong2 f refl refl = refl

  subst : {A : Set}(P : A → Set){x y : A} → x == y → P x → P y
  subst P refl Px = Px

module Lists where
  open Nats

  data List (A : Set) : Set where
    []   : List A
    _::_ : (x : A) -> (xs : List A) -> List A

  infixr 7 _::_

  [_] : ∀{A} -> A -> List A
  [ x ] = x :: []

  _++_ : ∀{A} -> List A -> List A -> List A
  (x :: xs) ++ ys = x :: xs ++ ys
  [] ++ ys = ys
  infixl 8 _++_

  length : forall {A} -> List A -> Nat
  length [] = 0
  length (x :: xs) = suc (length xs)

  repeat : forall {A} (x : A) (n : Nat) -> List A
  repeat x zero = []
  repeat x (suc n) = x :: repeat x n



module Vecs where
  open Nats

  data Vec (A : Set) : Nat -> Set where
    []   : Vec A 0
    _::_ : forall {n} -> (x : A) (xs : Vec A n) -> Vec A (suc n)

  infixr 7 _::_

  [_] : forall {A} -> A -> Vec A 1
  [ x ] = x :: []

  _++_ : forall {A n m} -> Vec A n -> Vec A m -> Vec A (n + m)
  _++_ {A} {zero} xs ys = ys
  _++_ {A} {suc n} (x :: xs) ys = x :: xs ++ ys

module Coinduction where

  postulate
    Lazy  : ∀ {a}(A : Set a) → Set a
    Thunk : ∀ {a}{A : Set a} → A → Lazy A
    Force : ∀ {a}{A : Set a} → Lazy A → A

  {-# BUILTIN INFINITY Lazy  #-}
  {-# BUILTIN SHARP    Thunk #-}
  {-# BUILTIN FLAT     Force #-}

module Unit where
  record Unit : Set where
    constructor <>

data Void : Set where

Not : Set -> Set
Not A = A -> Void

falseElim : {A : Set} -> Void -> A
falseElim ()

module Product where
  record _*_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _*_ public
  infixl 6 _*_
  infixl 6 _,_

module Sigma where
  record _**_ (A : Set) (P : A -> Set) : Set where
    constructor _,_
    field
      witness : A
      proof : P witness
  open _**_ public

module Sum where
  data Either (A B : Set) : Set where
    left : A -> Either A B
    right : B -> Either A B

  eitherCase : {A B C : Set} -> (A -> C) -> (B -> C) -> Either A B -> C
  eitherCase l r (left x) = l x
  eitherCase l r (right x) = r x

  eitherElim : {A B : Set} -> (C : Either A B -> Set)
             -> ((a : A) -> C (left a))
             -> ((b : B) -> C (right b))
             -> (x : Either A B) -> C x
  eitherElim C l r (left x) = l x
  eitherElim C l r (right x) = r x



module Decidable where
  data Dec (P : Set) : Set where
    yes : P -> Dec P
    no  : (P -> Void) -> Dec P
