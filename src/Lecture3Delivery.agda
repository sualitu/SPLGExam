module Lecture3Delivery where

open import Prelude

open Eq

module EquationalSyntax where
  _==[_]_ : {A : Set} (x : A) {y z : A} -> x == y -> y == z -> x == z
  x ==[ prf ] eq = trans prf eq

  infixr 2 _==[_]_

  _QED : {A : Set} (x : A) -> x == x
  x QED = refl

  infix 2 _QED

module EquationalExample where
  open EquationalSyntax
  open Nats

  +-assoc : forall n m o -> n + (m + o) == (n + m) + o
  +-assoc zero m o = refl
  +-assoc (suc n) m o = cong suc (+-assoc n m o)

  +-suc-r : forall n m -> n + suc m == suc (n + m)
  +-suc-r zero m = refl
  +-suc-r (suc n) m = cong suc (+-suc-r n m)

  +-comm : forall n m -> n + m == m + n
  +-comm zero zero = refl
  +-comm zero (suc m) = cong suc (+-comm 0 m)
  +-comm (suc n) m rewrite +-suc-r m n = cong suc (+-comm n m)

  test : (w x y z : Nat) -> (w + x) + (y + z) == (w + y) + (x + z)
  test w x y z = (w + x) + (y + z) ==[ sym (+-assoc w x (y + z)) ]
                 w + (x + (y + z)) ==[ cong (_+_ w) (+-assoc x y z) ]
                 w + ((x + y) + z) ==[ cong (λ n → w + (n + z)) (+-comm x y) ]
                 w + ((y + x) + z) ==[ cong (_+_ w) (sym (+-assoc y x z)) ]
                 w + (y + (x + z)) ==[ +-assoc w y (x + z) ]
                 ((w + y) + (x + z) QED)


module Isomorphisms where
  open EquationalSyntax

  data _<->_ (A : Set) (B : Set) : Set where
    isIso : (to : A -> B)
          -> (from : B -> A)
          -> (ok1 : (a : A) -> from (to a) == a)
          -> (ok2 : (b : B) -> to (from b) == b)
          -> A <-> B

  iso-refl : forall {A} -> A <-> A
  iso-refl = isIso id id (λ a → refl) (λ b → refl)

  iso-sym  : forall {A B} -> A <-> B -> B <-> A
  iso-sym (isIso to from ok1 ok2) = isIso from to ok2 ok1

  iso-trans : forall {A B C} -> A <-> B -> B <-> C -> A <-> C
  iso-trans (isIso to from ok1 ok2) (isIso to' from' ok1' ok2') =
    isIso (compose to to')
          (compose from' from)
          (λ a → from (from' (to' (to a))) ==[ cong from (ok1' (to a)) ]
                  from (to a) ==[ ok1 a ]
                  (a QED))
          (λ b → to' (to (from (from' b))) ==[ cong to' (ok2 (from' b)) ]
                 to' (from' b) ==[ ok2' b ]
                 (b QED))

  open Sum

  Either-Void-left : forall {A} -> Either Void A <-> A
  Either-Void-left = isIso to right ok1 (λ b → refl)
    where to : forall {A} -> Either Void A -> A
          to (left ())
          to (right x) = x
          ok1 : forall {A} -> (a : Either Void A) -> right (to a) == a
          ok1 (left ())
          ok1 (right x) = refl

--  Either-Void-right : forall {A} -> Either A Void <-> A
--  Either-Void-right = isIso ? ? ? ?

  Either-assoc : forall {A B C}
               -> Either (Either A B) C <-> Either A (Either B C)
  Either-assoc {A} {B} {C} = isIso to from to-from from-to
    where to : Either (Either A B) C -> Either A (Either B C)
          to (left (left x)) = left x
          to (left (right x)) = right (left x)
          to (right x) = right (right x)
          from : Either A (Either B C) -> Either (Either A B) C
          from (left x) = left (left x)
          from (right (left x)) = left (right x)
          from (right (right x)) = right x
          to-from : (a : Either (Either A B) C) → from (to a) == a
          to-from (left (left x)) = refl
          to-from (left (right x)) = refl
          to-from (right x) = refl
          from-to : (b : Either A (Either B C)) → to (from b) == b
          from-to (left x) = refl
          from-to (right (left x)) = refl
          from-to (right (right x)) = refl

  Either-comm : forall {A B} -> Either A B <-> Either B A
  Either-comm = isIso swap swap swap-swap swap-swap
    where swap : forall {A B} -> Either A B -> Either B A
          swap (left x) = right x
          swap (right x) = left x

          swap-swap : forall {A B} (x : Either A B) -> swap (swap x) == x
          swap-swap (left x) = refl
          swap-swap (right x) = refl

  Either-map : forall {A B A' B'}
             -> (A -> A') -> (B -> B')
             -> Either A B -> Either A' B'
  Either-map f g (left x) = left (f x)
  Either-map f g (right x) = right (g x)

  Either-cong : forall {A B A' B'}
              -> A <-> A'
              -> B <-> B'
              -> Either A B <-> Either A' B'
  Either-cong (isIso to from ok1 ok2) (isIso to' from' ok1' ok2') =
    isIso (Either-map to to')
          (Either-map from from')
          (λ { (left x) -> cong left (ok1 x) ;
              (right x) -> cong right (ok1' x) })
          (λ {(left x) → cong left (ok2 x);
              (right x) → cong right (ok2' x)})

module IsoDemo where
  open Isomorphisms
  open Nats
  open Fin
  open Vecs
  open Product
  open Unit
  open Lists

  IsEmpty : Set -> Set
  IsEmpty A = A <-> Void

  Fin0Empty : IsEmpty (Fin 0)
  Fin0Empty = isIso (λ ()) (λ ()) (λ ()) (λ ())




  Fin1Unit : Fin 1 <-> Unit
  Fin1Unit = isIso (λ x → <>) (λ x → zero) ok1 (λ u → refl)
    where ok1 : (a : Fin 1) -> zero == a
          ok1 zero = refl
          ok1 (suc ())



  Fin2Bool : Fin 2 <-> Bool
  Fin2Bool = isIso to from ok1 ok2
    where to : Fin 2 -> Bool
          to zero = false
          to (suc zero) = true
          to (suc (suc ()))
          from : Bool -> Fin 2
          from true = suc zero
          from false = zero
          ok1 : (a : Fin 2) -> (from (to a)) == a
          ok1 zero = refl
          ok1 (suc zero) = refl
          ok1 (suc (suc ()))
          ok2 : (b : Bool) -> (to (from b)) == b
          ok2 true = refl
          ok2 false = refl


  

  -- NatListUnit : Nat <-> List Unit
  -- NatListUnit = isIso (repeat <>) length repeatLen {!!}
  --   where repeatLen : (n : Nat) -> length (repeat <> n) == n
  --         repeatLen zero = refl
  --         repeatLen (suc n) = cong suc (repeatLen n)

  --         lengthRepeat : (xs : List Unit) -> repeat <> (length xs) == xs
  --         lengthRepeat [] = refl
  --         lengthRepeat (<> :: xs) = cong (_::_ <>) (lengthRepeat xs)






module IsomorphismSyntax where
  open Isomorphisms
  _QED : (A : Set) -> A <-> A
  _QED A = iso-refl

  infix 2 _QED

  _<->[_]_ : (A : Set) {B C : Set} -> A <-> B -> B <-> C -> A <-> C
  a <->[ step ] c = iso-trans step c

  infixr 2 _<->[_]_


module BagEquality where
  open Lists
  open Sum
  open Decidable

  data Elem' {A : Set} (x : A) : List A -> Set where
    here : forall {xs} -> Elem' x (x :: xs)
    there : forall {y xs} -> Elem' x xs -> Elem' x (y :: xs)

  Any : forall {A} -> (A -> Set) -> List A -> Set
  Any P [] = Void
  Any P (x :: xs) = Either (P x) (Any P xs)

  Elem : forall {A} (x : A) (xs : List A) -> Set
  Elem x xs = Any (λ y → x == y) xs

  open Isomorphisms

  _=bag_ : forall {A} -> List A -> List A -> Set
  xs =bag ys = (z : _) → Elem z xs <-> Elem z ys

  =bag-refl : forall {A} {xs : List A} -> xs =bag xs
  =bag-refl x = iso-refl

  =bag-sym : forall {A}{xs ys : List A} -> xs =bag ys -> ys =bag xs
  =bag-sym h x = iso-sym (h x)

  -- =bag-trans - watch that hand wave!

  open IsomorphismSyntax

  Any-++ : forall {A} -> (P : A -> Set) -> (xs ys : List A)
         -> Any P (xs ++ ys) <-> Either (Any P xs) (Any P ys)
  Any-++ P [] ys = iso-sym Either-Void-left
  Any-++ P (x :: xs) ys =
    Either (P x) (Any P (xs ++ ys))             <->[
                 Either-cong iso-refl (Any-++ P xs ys) ]
    Either (P x) (Either (Any P xs) (Any P ys)) <->[
                 iso-sym Either-assoc ]
    (Either (Any P (x :: xs)) (Any P ys)        QED)


  ++-bag-comm : forall {A} -> (xs ys : List A)
              -> (xs ++ ys) =bag (ys ++ xs)
  ++-bag-comm xs ys =
    λ elt → Any (_==_ elt) (xs ++ ys) <->[ Any-++ _ xs ys ]
            Either (Elem elt xs) (Elem elt ys) <->[ Either-comm ]
            Either (Elem elt ys) (Elem elt xs) <->[
                     iso-sym (Any-++ _ ys xs) ]
            (Any (_==_ elt) (ys ++ xs) QED)
