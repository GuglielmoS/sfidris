module Basics

data Day = Monday
         | Tuesday
         | Wednesday
         | Thursday
         | Friday
         | Saturday
         | Sunday

nextWeekDay : Day -> Day
nextWeekDay Monday = Tuesday 
nextWeekDay Tuesday = Wednesday 
nextWeekDay Wednesday = Thursday 
nextWeekDay Thursday = Friday 
nextWeekDay Friday = Saturday 
nextWeekDay Saturday = Sunday 
nextWeekDay Sunday = Monday 

testNextWeekDay : nextWeekDay (nextWeekDay Saturday) = Monday
testNextWeekDay = Refl

-- booleans

-- data Bool : Type where
--   True : Bool
--   False : Bool

-- alernatively
--   data Bool = True | False

negb : Bool -> Bool
negb True = False
negb False = True

andb : Bool -> Bool -> Bool
andb True b2 = b2 
andb False _ = False

orb : Bool -> Bool -> Bool
orb True _ = True
orb False b2 = b2 

-- orb's truth table

orbOkWithFF : orb False False = False
orbOkWithFF = Refl

orbOkWithFT : orb False True = True
orbOkWithFT = Refl

orbOkWithTF : orb True False = True
orbOkWithTF = Refl

orbOkWithTT : orb True True = True
orbOkWithTT = Refl

-- Exercise NANDB

nandb : Bool -> Bool -> Bool
nandb b1 b2 = negb $ andb b1 b2

nandbOkWithFF : nandb False False = True
nandbOkWithFF = Refl

nandbOkWithFT : nandb False True = True
nandbOkWithFT = Refl

nandbOkWithTF : nandb True False = True
nandbOkWithTF = Refl

nandbOkWithTT : nandb True True = False
nandbOkWithTT = Refl

-- Exercise ANDB3

andb3 : Bool -> Bool -> Bool -> Bool
andb3 b1 b2 b3 = andb (andb b1 b2) b3

andb3OkWithTTT : andb3 True True True = True
andb3OkWithTTT = Refl

andb3OkWithFTT : andb3 False True True = False
andb3OkWithFTT = Refl

andb3OkWithTFT : andb3 True False True = False
andb3OkWithTFT = Refl

andb3OkWithTTF : andb3 True True False = False
andb3OkWithTTF = Refl

namespace Playground1
  data Nat' : Type where
    O : Nat'         -- zero
    S' : Nat' -> Nat'  -- successor

-- alterntively
-- data Nat' = O | S Nat' 

  pred : Nat' -> Nat'
  pred O = O
  pred (S' x) = x

minusTwo : Nat -> Nat
minusTwo Z = Z
minusTwo (S Z) = Z
minusTwo (S (S x)) = x

evenb : Nat -> Bool
evenb Z = True
evenb (S Z) = False
evenb (S (S x)) = evenb x

oddb : Nat -> Bool
oddb = negb . evenb

testZddb1 : oddb (S Z) = True
testZddb1 = Refl

testZddb2 : oddb (S (S (S (S Z)))) = False
testZddb2 = Refl

namespace Playground2
  plus' : Nat -> Nat -> Nat
  plus' Z     m = m
  plus' (S n) m = S (plus' n m)

  mult' : Nat -> Nat -> Nat
  mult' Z m = Z 
  mult' (S n) m = plus' m (mult' n m) 

  testMult1 : mult' (S (S (S Z))) (S (S (S Z))) = (S (S (S (S (S (S (S (S (S Z))))))))) 
  testMult1 = Refl

  minus' : Nat -> Nat -> Nat
  minus' Z _ = Z
  minus' n@(S _) Z = n
  minus' (S n) (S m) = minus' n m


exp : Nat -> Nat -> Nat
exp base Z = S Z
exp base (S p) = mult base (exp base p)

-- Exercise FACTZRIAL

factorial : Nat -> Nat
factorial Z = S Z
factorial n@(S n') = mult n (factorial n')

testFactorial1 : factorial (S (S (S Z))) = S (S (S (S (S (S Z)))))
testFactorial1 = Refl

ten : Nat
ten = S (S (S (S (S (S (S (S (S (S Z)))))))))

twelve : Nat
twelve = plus ten (S (S Z))

testFactorial2 : factorial (S (S (S (S (S Z))))) = mult ten twelve 
testFactorial2 = Refl

-- Exercise End

beqNat : Nat -> Nat -> Bool
beqNat Z Z = True
beqNat Z (S _) = False
beqNat (S n) Z = False
beqNat (S n) (S m) = beqNat n m 

bleNat : Nat -> Nat -> Bool
bleNat Z _ = True
bleNat (S n) Z = False 
bleNat (S n) (S m) = bleNat n m

testBleNat1 : bleNat (S (S Z)) (S (S Z)) = True
testBleNat1 = Refl

testBleNat2 : bleNat (S (S Z)) (S (S (S (S Z)))) = True
testBleNat2 = Refl

testBleNat3 : bleNat (S (S (S (S Z)))) (S (S Z)) = False
testBleNat3 = Refl

-- Exercise BLT_NAT

bltNat : Nat -> Nat -> Bool
bltNat n m = andb (bleNat n m) (negb $ beqNat n m)

testBltNat1 : bltNat (S (S Z)) (S (S Z)) = False
testBltNat1 = Refl

testBltNat2 : bltNat (S (S Z)) (S (S (S (S Z)))) = True
testBltNat2 = Refl

testBltNat3 : bltNat (S (S (S (S Z)))) (S (S Z)) = False
testBltNat3 = Refl

-- End Exercise

plusZeroLeft : plus Z n = n
plusZeroLeft = Refl

plusZneLeft : plus (S Z) n = S n
plusZneLeft = Refl

multZeroLeft : mult Z n = Z
multZeroLeft = Refl

plusIdExample : n = m -> n + m = m + m
plusIdExample nEQm = rewrite nEQm in Refl 

-- Exercise PLUSID

plusIdExercise : n = m -> m = o -> n + m = m + o
plusIdExercise nEQm mEQo = rewrite nEQm in rewrite mEQo in Refl

-- Exercise End

multZeroPlus : mult (plus Z n) m = mult n m
multZeroPlus = Refl

-- Exercise MUTL_S_1

multSuccZne : m = S n -> mult m (plus (S Z) n) = mult m m
multSuccZne mEQSN = rewrite mEQSN in Refl

-- Exercise End

plusZneNeqZero : (n : Nat) -> beqNat (plus n (S Z)) Z = False
plusZneNeqZero Z = Refl
plusZneNeqZero (S _) = Refl

negbInvolutive : (b : Bool) -> negb (negb b) = b
negbInvolutive True = Refl
negbInvolutive False = Refl

-- Exercise Zero_nbeq_PlusZne

zeroNbeqPlusZne : (n : Nat) -> beqNat Z (plus n (S Z)) = False
zeroNbeqPlusZne Z = Refl
zeroNbeqPlusZne (S _) = Refl

-- Exercise End

-- Exercise BooleanFunctions

identityFnAppliedTwice : 
  (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> ((b : Bool) -> f (f b) = b)
identityFnAppliedTwice f fxEQx b = rewrite fxEQx b in rewrite fxEQx b in Refl

negationFnAppliedTwice :
  (f : Bool -> Bool) -> ((x : Bool) -> f x = negb x) -> ((b : Bool) -> f (f b) = b)
negationFnAppliedTwice f fxIsNegbx b = rewrite fxIsNegbx b in 
                                       rewrite fxIsNegbx (negb b) in 
                                       negbInvolutive b 

-- Exercise End

-- Exercise ANDB_EQ_ZRB

--andbEQorb : (b : Bool) -> (c : Bool) -> andb b c = orb b c -> b = c
--andbEQorb False False _ = Refl
--andbEQorb False True contra = contra
--andbEQorb True False contra = ?todo
--andbEQorb True True _ = Refl

-- Exercise End

-- Exercise BINARY

data Bin : Type where
  Zero : Bin
  TwiceBin : Bin -> Bin
  OneMoreThanTwice : Bin -> Bin

incr : Bin -> Bin
incr Zero = OneMoreThanTwice Zero
incr (TwiceBin x) = OneMoreThanTwice x
incr (OneMoreThanTwice x) = TwiceBin (incr x)

binToNat : Bin -> Nat
binToNat Zero = Z 
binToNat (TwiceBin x) = mult (S (S Z)) $ binToNat x 
binToNat (OneMoreThanTwice x) = plus (S Z) (mult (S (S Z)) (binToNat x))

testBinIncr1 : binToNat (incr Zero) = S Z
testBinIncr1 = Refl

testBinIncr2 : binToNat (incr $ TwiceBin Zero) = S Z
testBinIncr2 = Refl

testBinIncr3 : binToNat (incr $ OneMoreThanTwice Zero) = S (S Z)
testBinIncr3 = Refl

--testBinIncr4 : (n : Bin) -> binToNat (incr n) = plus (S Z) (binToNat n)
--testBinIncr4 Zero = Refl
--testBinIncr4 (TwiceBin x) = Refl
--testBinIncr4 (OneMoreThanTwice x) = ?testBinIncr4_rhs_4
