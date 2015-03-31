module NatList

import Basics
import Induction

data NatProd : Type where
  pair : Nat -> Nat -> NatProd

first : NatProd -> Nat
first (pair x _) = x 

second : NatProd -> Nat
second (pair _ y) = y 

swapPair : NatProd -> NatProd
swapPair (pair x y) = pair y x 

surjectivePairing' : (n, m : Nat) -> pair n m = pair (first (pair n m)) (second (pair n m))
surjectivePairing' n m = Refl

surjectivePairing : (p : NatProd) -> p = pair (first p) (second p)
surjectivePairing (pair x y) = Refl

-- Exercise SndFstIsSwap

secondFirstIsSwap : (p : NatProd) -> pair (second p) (first p) = swapPair p
secondFirstIsSwap (pair x y) = Refl

-- Exercise End

-- Exercise FstSwapIsSnd

firstSwapIsSecond : (p : NatProd) -> first (swapPair p) = second p
firstSwapIsSecond (pair x y) = Refl

-- Exercise End

data NatList : Type where
  NatNil : NatList
  NatCons : Nat -> NatList -> NatList

repeat' : Nat -> Nat -> NatList
repeat' n Z = NatNil
repeat' n (S k) = NatCons n (repeat' n k)

length' : NatList -> Nat
length' NatNil = 0
length' (NatCons _ xs) = 1 + length' xs 

app : NatList -> NatList -> NatList
app NatNil ys = ys
app (NatCons x xs) ys = NatCons x (app xs ys) 

testApp1 : app (NatCons 1 (NatCons 2 (NatCons 3 NatNil))) 
               (NatCons 4 (NatCons 5 NatNil))
           = (NatCons 1 (NatCons 2 (NatCons 3 (NatCons 4 (NatCons 5 NatNil)))))
testApp1 = Refl

testApp2 : app NatNil (NatCons 4 (NatCons 5 NatNil)) = (NatCons 4 (NatCons 5 NatNil))
testApp2 = Refl

testApp3 : app (NatCons 1 (NatCons 2 (NatCons 3 NatNil))) NatNil = NatCons 1 (NatCons 2 (NatCons 3 NatNil))
testApp3 = Refl

hd : Nat -> NatList -> Nat
hd default NatNil = default
hd _ (NatCons x _) = x

tl : NatList -> NatList
tl NatNil = NatNil
tl (NatCons _ xs) = xs

testHd1 : hd 0 (NatCons 1 (NatCons 2 (NatCons 3 NatNil))) = 1 
testHd1 = Refl

testHd2 : hd 0 NatNil = 0
testHd2 = Refl

testTl : tl (NatCons 1 (NatCons 2 (NatCons 3 NatNil))) = NatCons 2 (NatCons 3 NatNil)
testTl = Refl

-- Exercise ListFuns

nonZeros : NatList -> NatList
nonZeros NatNil = NatNil
nonZeros (NatCons x xs) = if beqNat x 0
                          then nonZeros xs
                          else NatCons x $ nonZeros xs

testNonZeros : nonZeros (NatCons 0 (NatCons 1 (NatCons 0 (NatCons 2 (NatCons 3 (NatCons 0
                        (NatCons 0 NatNil)))))))
               = (NatCons 1 (NatCons 2 (NatCons 3 NatNil)))
testNonZeros = Refl

oddMembers : NatList -> NatList
oddMembers NatNil = NatNil
oddMembers (NatCons x xs) = if oddb x
                            then NatCons x $ oddMembers xs
                            else oddMembers xs

testOddMembers : oddMembers (NatCons 0 (NatCons 1 (NatCons 0 (NatCons 2 (NatCons 3 (NatCons 0
                            (NatCons 0 NatNil)))))))
               = (NatCons 1 (NatCons 3 NatNil))
testOddMembers = Refl

countOddMembers : NatList -> Nat
countOddMembers = length' . oddMembers 

testCountOddMembers1 : countOddMembers (NatCons 1 (NatCons 0 (NatCons 3 (NatCons 1 
                                       (NatCons 4 (NatCons 5 NatNil)))))) = 4
testCountOddMembers1 = Refl

testCountOddMembers2 : countOddMembers (NatCons 0 (NatCons 2 (NatCons 4 NatNil))) = 0
testCountOddMembers2 = Refl

testCountOddMembers3 : countOddMembers NatNil = 0
testCountOddMembers3 = Refl

-- Exercise End

Bag : Type
Bag = NatList

count : Nat -> Bag -> Nat
count v NatNil = 0
count v (NatCons x xs) = if beqNat v x
                         then 1 + count v xs
                         else count v xs

testCount1 : count 1 (NatCons 1 (NatCons 2 (NatCons 3 (NatCons 1 (NatCons 4
                     (NatCons 1 NatNil)))))) = 3
testCount1 = Refl

testCount2 : count 6 (NatCons 1 (NatCons 2 (NatCons 3 (NatCons 1 (NatCons 4
                     (NatCons 1 NatNil)))))) = 0
testCount2 = Refl

sum' : Bag -> Bag -> Bag
sum' = app

testSum1 : count 1 (sum' (NatCons 1 (NatCons 2 (NatCons 3 NatNil)))
                         (NatCons 1 (NatCons 4 (NatCons 1 NatNil)))) = 3
testSum1 = Refl

add : Nat -> Bag -> Bag
add = NatCons

testAdd1 : count 1 (add 1 (NatCons 1 (NatCons 4 (NatCons 1 NatNil)))) = 3
testAdd1 = Refl

testAdd2 : count 5 (add 1 (NatCons 1 (NatCons 4 (NatCons 1 NatNil)))) = 0
testAdd2 = Refl

member : Nat -> Bag -> Bool
member v xs = negb $ beqNat (count v xs) 0

testMember1 : member 1 (NatCons 1 (NatCons 4 (NatCons 1 NatNil))) = True
testMember1 = Refl
 
testMember2 : member 2 (NatCons 1 (NatCons 4 (NatCons 1 NatNil))) = False
testMember2 = Refl
 
-- Reasoning About Lists

nilApp : (l : NatList) -> app NatNil l = l 
nilApp l = Refl

tlLengthPred : (l : NatList) -> pred (length' l) = length' (tl l)
tlLengthPred NatNil         = Refl
tlLengthPred (NatCons x xs) = Refl

appAssoc : (l1, l2, l3 : NatList) -> app (app l1 l2) l3 = app l1 (app l2 l3)
appAssoc NatNil         l2 l3 = Refl
appAssoc (NatCons x xs) l2 l3 = cong $ appAssoc xs l2 l3

appLength : (l1, l2 : NatList) -> length' (app l1 l2) = length' l1 + length' l2
appLength NatNil         l2 = Refl
appLength (NatCons x xs) l2 = cong $ appLength xs l2

-- Reversing a list

snoc : NatList -> Nat -> NatList
snoc NatNil         v = NatCons v NatNil
snoc (NatCons x xs) v = NatCons x $ snoc xs v

rev : NatList -> NatList
rev NatNil         = NatNil
rev (NatCons x xs) = snoc (rev xs) x

testRev1 : rev (NatCons 1 (NatCons 2 (NatCons 3 NatNil)))
           = (NatCons 3 (NatCons 2 (NatCons 1 NatNil)))
testRev1 = Refl

testRev2 : rev NatNil = NatNil
testRev2 = Refl

lengthSnoc : (n : Nat) -> (l : NatList) -> length' (snoc l n) = S (length' l)
lengthSnoc n NatNil         = Refl
lengthSnoc n (NatCons x xs) = cong $ lengthSnoc n xs

revLength : (l : NatList) -> length' (rev l) = length' l
revLength NatNil         = Refl
revLength (NatCons x xs) = rewrite lengthSnoc x (rev xs) in cong $ revLength xs

-- List Exercises, Part 1

appNilEnd : (l : NatList) -> app l NatNil = l
appNilEnd NatNil         = Refl
appNilEnd (NatCons x xs) = rewrite appNilEnd xs in Refl

beqNatList : NatList -> NatList -> Bool
beqNatList NatNil NatNil = True
beqNatList NatNil _      = False
beqNatList _      NatNil = False
beqNatList (NatCons x xs) (NatCons y ys) = if beqNat x y
                                           then beqNatList xs ys
                                           else False

testBeqNatList1 : beqNatList NatNil NatNil = True
testBeqNatList1 = Refl

testBeqNatList2 : beqNatList (NatCons 1 (NatCons 2 (NatCons 3 NatNil)))
                             (NatCons 1 (NatCons 2 (NatCons 3 NatNil))) = True
testBeqNatList2 = Refl

testBeqNatList3 : beqNatList (NatCons 1 (NatCons 2 (NatCons 3 NatNil)))
                             (NatCons 1 (NatCons 2 (NatCons 4 NatNil))) = False
testBeqNatList3 = Refl

beqNatListRefl : (l : NatList) -> True = beqNatList l l
beqNatListRefl NatNil         = Refl
beqNatListRefl (NatCons x xs) = rewrite sym $ beqNatRefl x in 
                                rewrite beqNatListRefl xs in Refl

-- Options

data NatOption : Type where
  None : NatOption
  Some : Nat -> NatOption

index : Nat -> NatList -> NatOption
index _ NatNil         = None 
index n (NatCons x xs) = if beqNat n 0 then Some x else index (pred n) xs 

testIndex1 : index 0 (NatCons 4 (NatCons 5 (NatCons 6 (NatCons 7 NatNil)))) = Some 4
testIndex1 = Refl

testIndex2 : index 3 (NatCons 4 (NatCons 5 (NatCons 6 (NatCons 7 NatNil)))) = Some 7
testIndex2 = Refl

testIndex3 : index 10 (NatCons 4 (NatCons 5 (NatCons 6 (NatCons 7 NatNil)))) = None
testIndex3 = Refl

optionElim : Nat -> NatOption -> Nat
optionElim default None     = default 
optionElim default (Some n) = n

-- Exercise HD_OPT

hdOpt : NatList -> NatOption
hdOpt NatNil        = None
hdOpt (NatCons h _) = Some h

testHdOpt1 : hdOpt NatNil = None
testHdOpt1 = Refl

testHdOpt2 : hdOpt (NatCons 1 NatNil) = Some 1
testHdOpt2 = Refl

testHdOpt3 : hdOpt (NatCons 5 (NatCons 6 NatNil)) = Some 5
testHdOpt3 = Refl

-- Exercise End

-- Exercise OptionElimHd

optionElimHd : (l : NatList) -> (default : Nat) ->
               hd default l = optionElim default (hdOpt l)
optionElimHd NatNil         default = Refl
optionElimHd (NatCons x xs) default = Refl

-- Exercise End

-- Dictionaries

data Dictionary : Type where
  Empty : Dictionary
  Record : Nat -> Nat -> Dictionary -> Dictionary

insert : Nat -> Nat -> Dictionary -> Dictionary
insert = Record

find : Nat -> Dictionary -> NatOption
find key Empty          = None
find key (Record k v d) = if beqNat k key then Some v else find key d

-- Exercises

dictionaryInvariant1' : (d : Dictionary) -> (k, v : Nat) -> find k (insert k v d) = Some v
dictionaryInvariant1' d k v = rewrite sym $ beqNatRefl k in Refl

dictionaryInvariant2' : (d : Dictionary) -> (m, n, o : Nat) -> 
                        beqNat n m = False -> find m d = find m (insert n o d)
dictionaryInvariant2' d m n o nNEQm = rewrite nNEQm in Refl
