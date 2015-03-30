module Basics

%hide Prelude.Bool.Bool
%hide Prelude.Nat.Nat

%default total

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

data Bool : Type where
  True : Bool
  False : Bool

-- alernatively
-- data Bool = True | False

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

data Nat : Type where
  O : Nat         -- zero
  S : Nat -> Nat  -- successor

-- alterntively
-- data Nat = O | S Nat 

pred : Nat -> Nat
pred O = O
pred (S x) = x

minusTwo : Nat -> Nat
minusTwo O = O
minusTwo (S O) = O
minusTwo (S (S x)) = x

evenb : Nat -> Bool
evenb O = True
evenb (S O) = False
evenb (S (S x)) = evenb x

oddb : Nat -> Bool
oddb = negb . evenb

testOddb1 : oddb (S O) = True
testOddb1 = Refl

testOddb2 : oddb (S (S (S (S O)))) = False
testOddb2 = Refl

plus : Nat -> Nat -> Nat
plus O      m = m
plus (S n) m = S (plus n m)

mult : Nat -> Nat -> Nat
mult O m = O 
mult (S n) m = plus m (mult n m) 

testMult1 : mult (S (S (S O))) (S (S (S O))) = (S (S (S (S (S (S (S (S (S O))))))))) 
testMult1 = Refl

minus : Nat -> Nat -> Nat
minus O _ = O
minus n@(S _) O = n
minus (S n) (S m) = minus n m

exp : Nat -> Nat -> Nat
exp base O = S O
exp base (S p) = mult base (exp base p)

-- Exercise FACTORIAL

factorial : Nat -> Nat
factorial O = S O
factorial n@(S n') = mult n (factorial n')

testFactorial1 : factorial (S (S (S O))) = S (S (S (S (S (S O)))))
testFactorial1 = Refl

ten : Nat
ten = S (S (S (S (S (S (S (S (S (S O)))))))))

twelve : Nat
twelve = plus ten (S (S O))

testFactorial2 : factorial (S (S (S (S (S O))))) = mult ten twelve 
testFactorial2 = Refl

-- Exercise End

beqNat : Nat -> Nat -> Bool
beqNat O O = True
beqNat O (S _) = False
beqNat (S n) O = False
beqNat (S n) (S m) = beqNat n m 

bleNat : Nat -> Nat -> Bool
bleNat O _ = True
bleNat (S n) O = False 
bleNat (S n) (S m) = bleNat n m

testBleNat1 : bleNat (S (S O)) (S (S O)) = True
testBleNat1 = Refl

testBleNat2 : bleNat (S (S O)) (S (S (S (S O)))) = True
testBleNat2 = Refl

testBleNat3 : bleNat (S (S (S (S O)))) (S (S O)) = False
testBleNat3 = Refl

-- Exercise BLT_NAT

bltNat : Nat -> Nat -> Bool
bltNat n m = andb (bleNat n m) (negb $ beqNat n m)

testBltNat1 : bltNat (S (S O)) (S (S O)) = False
testBltNat1 = Refl

testBltNat2 : bltNat (S (S O)) (S (S (S (S O)))) = True
testBltNat2 = Refl

testBltNat3 : bltNat (S (S (S (S O)))) (S (S O)) = False
testBltNat3 = Refl

-- End Exercise

plusZeroLeft : plus O n = n
plusZeroLeft = Refl

plusOneLeft : plus (S O) n = S n
plusOneLeft = Refl

multZeroLeft : mult O n = O
multZeroLeft = Refl

plusIdExample : n = m -> n + m = m + m
plusIdExample nEQm = rewrite nEQm in Refl 

-- Exercise PLUSID

plusIdExercise : n = m -> m = o -> n + m = m + o
plusIdExercise nEQm mEQo = rewrite nEQm in rewrite mEQo in Refl

-- Exercise End

multZeroPlus : mult (plus O n) m = mult n m
multZeroPlus = Refl

-- Exercise MUTL_S_1

multSuccOne : m = S n -> mult m (plus (S O) n) = mult m m
multSuccOne mEQSN = rewrite mEQSN in Refl

-- Exercise End

plusOneNeqZero : (n : Nat) -> beqNat (plus n (S O)) O = False
plusOneNeqZero O = Refl
plusOneNeqZero (S _) = Refl

negbInvolutive : (b : Bool) -> negb (negb b) = b
negbInvolutive True = Refl
negbInvolutive False = Refl

-- Exercise Zero_nbeq_PlusOne

zeroNbeqPlusOne : (n : Nat) -> beqNat O (plus n (S O)) = False
zeroNbeqPlusOne O = Refl
zeroNbeqPlusOne (S _) = Refl

-- Exercise End

-- Exercise BooleanFunctions

identityFnAppliedTwice : 
  (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> ((b : Bool) -> f (f b) = b)
identityFnAppliedTwice f fxEQx b = rewrite fxEQx b in rewrite fxEQx b in Refl

--negationFnAppliedTwice :
--  (f : Bool -> Bool) -> ((x : Bool) -> f x = negb x) -> ((b : Bool) -> f (f b) = b)
-- TODO

-- Exercise End

-- Exercise ANDB_EQ_ORB

--andbEQorb : (b : Bool) -> (c : Bool) -> andb b c = orb b c -> b = c
-- TODO

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
binToNat Zero = O 
binToNat (TwiceBin x) = mult (S (S O)) $ binToNat x 
binToNat (OneMoreThanTwice x) = plus (S O) (mult (S (S O)) (binToNat x))

testBinIncr1 : binToNat (incr Zero) = S O
testBinIncr1 = Refl

testBinIncr2 : binToNat (incr $ TwiceBin Zero) = S O
testBinIncr2 = Refl

testBinIncr3 : binToNat (incr $ OneMoreThanTwice Zero) = S (S O)
testBinIncr3 = Refl

testBinIncr4 : (n : Bin) -> binToNat (incr n) = plus (S O) (binToNat n)
testBinIncr4 Zero = Refl
testBinIncr4 (TwiceBin x) = Refl
testBinIncr4 (OneMoreThanTwice x) = ?testBinIncr4_rhs_4
-- TODO

