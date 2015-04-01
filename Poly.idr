module Poly

%hide Prelude.List.List

data List : Type -> Type where
  Nil  : List x
  Cons : x -> List x -> List x

length : List x -> Nat
length Nil         = 0
length (Cons _ xs) = 1 + length xs

testLength1 : length (Cons 1 (Cons 2 Nil)) = 2
testLength1 = Refl

testLength2 : length (Cons True Nil) = 1
testLength2 = Refl

append : List x -> List x -> List x
append Nil         ys = ys
append (Cons x xs) ys = Cons x $ append xs ys

snoc : List x -> x -> List x
snoc Nil         v = Cons v Nil
snoc (Cons x xs) v = Cons x $ snoc xs v

rev : List x -> List x
rev Nil         = Nil
rev (Cons x xs) = snoc (rev xs) x 

testRev1 : rev (Cons 1 (Cons 2 Nil)) = Cons 2 (Cons 1 Nil)
testRev1 = Refl

testRev2 : rev Nil = Nil
testRev2 = Refl
