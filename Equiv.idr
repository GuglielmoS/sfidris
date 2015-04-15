module Equiv

import Imp
import Logic

%default total

aequiv : {st : State} -> AExp -> AExp -> Type
aequiv {st} a1 a2 = (aeval st a1 = aeval st a2)

bequiv : {st : State} -> BExp -> BExp -> Type
bequiv {st} b1 b2 = (beval st b1 = beval st b2)

cequiv : {st : State} -> {st' : State} -> Com -> Com -> Type
cequiv {st} {st'} c1 c2 = (ceval c1 st st') <-> (ceval c2 st st')

skipLeft : cequiv (CSeq CSkip c) c
skipLeft = conj skipLeft_rhs1 skipLeft_rhs2
  where -- Case ->
        skipLeft_rhs1 : ceval (CSeq CSkip c) st st' -> ceval c st st'
        skipLeft_rhs1 (E_Seq E_SKip rest) = rest
        -- Case <-
        skipLeft_rhs2 : ceval c st st' -> ceval (CSeq CSkip c) st st'
        skipLeft_rhs2 {c = CSkip} evalc = E_Seq evalc E_SKip
        skipLeft_rhs2 {c = (CAss k x)} evalc = E_Seq E_SKip evalc
        skipLeft_rhs2 {c = (CSeq x y)} evalc = E_Seq E_SKip evalc
        skipLeft_rhs2 {c = (CIf x y z)} evalc = E_Seq E_SKip evalc
        skipLeft_rhs2 {c = (CWhile x y)} evalc = E_Seq E_SKip evalc

-- Behavioral Equivalence is an Equivalence

reflAequiv : aequiv a a
reflAequiv = Refl

symAequiv : aequiv {st} a1 a2 -> aequiv {st} a2 a1
symAequiv equiv = sym equiv

transAequiv : aequiv {st} a1 a2 -> aequiv {st} a2 a3 -> aequiv {st} a1 a3
transAequiv equiv12 equiv23  = rewrite equiv12 in equiv23

reflBequiv : bequiv b b
reflBequiv = Refl

symBequiv : bequiv {st} b1 b2 -> bequiv {st} b2 b1
symBequiv equiv = sym equiv

transBequiv : bequiv {st} b1 b2 -> bequiv {st} b2 b3 -> bequiv {st} b1 b3
transBequiv equiv12 equiv23  = rewrite equiv12 in equiv23

reflCequiv : cequiv {st} {st'} c c
reflCequiv = conj impliesTheSame impliesTheSame
  where impliesTheSame : ceval c st st' -> ceval c st st'
        impliesTheSame prf = prf

symCequiv : cequiv {st} {st'} c1 c2 -> cequiv {st} {st'} c2 c1
symCequiv equiv = conj (symEquivLeft equiv) (symCequivRight equiv)
  where -- Case ->
        symEquivLeft : cequiv {st} {st'} c1 c2 -> ceval c2 st st' -> ceval c1 st st'
        symEquivLeft (conj _ toC1) c2eval = toC1 c2eval
        -- Case <-
        symCequivRight : cequiv {st} {st'} c1 c2 -> ceval c1 st st' -> ceval c2 st st'
        symCequivRight (conj toC2 _) c1eval = toC2 c1eval

transCequiv : cequiv {st} {st'} c1 c2 -> cequiv {st} {st'} c2 c3 -> cequiv {st} {st'} c1 c3
transCequiv c1EQUIVc2 c2EQUIVc3 = iffTrans c1EQUIVc2 c2EQUIVc3

--
-- Behavioral Equivalence is a Congruence
--

-- Assignment is a congruenge

CAssCongLeft : aequiv {st} a1 a1' -> ceval (CAss i a1) st st' -> ceval (CAss i a1') st st'
CAssCongLeft {st} aEQUIVa' (E_Ass prf) = ?CAssCongLeftProof 
Equiv.CAssCongLeftProof = proof
  intros
  rewrite prf
  refine E_Ass
  rewrite aEQUIVa'
  trivial

CAssCongRight : aequiv {st} a1 a1' -> ceval (CAss i a1') st st' -> ceval (CAss i a1) st st'
CAssCongRight {st} aEQUIVa' (E_Ass prf) = ?CAssCongRightProof
Equiv.CAssCongRightProof = proof
  intros
  rewrite prf
  refine E_Ass
  rewrite sym aEQUIVa'
  trivial

CAssCong : aequiv {st} a1 a1' -> cequiv {st} {st'} (CAss i a1) (CAss i a1') 
CAssCong {st} {st'} {a1} {a1'} x = conj (CAssCongLeft x) (CAssCongRight x)

--
-- CONSTANT FOLDING
--

optimizedPlus : AExp -> AExp -> AExp
optimizedPlus (ANum n) (ANum m) = ANum (n + m)
optimizedPlus (ANum Z) e = e
optimizedPlus e (ANum Z) = e
optimizedPlus e1 e2 = APlus e1 e2

optimizedPlusIsCorrect : plus (aeval st a1) (aeval st a2) = aeval st (optimizedPlus a1 a2) 
optimizedPlusIsCorrect {a1 = (ANum k)} {a2 = (ANum j)} = Refl
optimizedPlusIsCorrect {a1 = (ANum Z)} {a2 = (AId j)} = Refl
optimizedPlusIsCorrect {a1 = (ANum (S k))} {a2 = (AId j)} = Refl
optimizedPlusIsCorrect {a1 = (ANum Z)} {a2 = (APlus x y)} = Refl
optimizedPlusIsCorrect {a1 = (ANum (S k))} {a2 = (APlus x y)} = Refl
optimizedPlusIsCorrect {a1 = (ANum Z)} {a2 = (AMinus x y)} = Refl
optimizedPlusIsCorrect {a1 = (ANum (S k))} {a2 = (AMinus x y)} = Refl
optimizedPlusIsCorrect {a1 = (ANum Z)} {a2 = (AMult x y)} = Refl
optimizedPlusIsCorrect {a1 = (ANum (S k))} {a2 = (AMult x y)} = Refl
optimizedPlusIsCorrect {st} {a1 = (AId k)} {a2 = (ANum Z)} = rewrite plusZeroRightNeutral (st k) in Refl
optimizedPlusIsCorrect {a1 = (AId k)} {a2 = (ANum (S j))} = Refl
optimizedPlusIsCorrect {a1 = (AId k)} {a2 = (AId j)} = Refl
optimizedPlusIsCorrect {a1 = (AId k)} {a2 = (APlus x y)} = Refl
optimizedPlusIsCorrect {a1 = (AId k)} {a2 = (AMinus x y)} = Refl
optimizedPlusIsCorrect {a1 = (AId k)} {a2 = (AMult x y)} = Refl
optimizedPlusIsCorrect {st} {a1 = (APlus x y)} {a2 = (ANum Z)} = rewrite plusZeroRightNeutral (plus (aeval st x) (aeval st y)) in Refl
optimizedPlusIsCorrect {a1 = (APlus x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusIsCorrect {a1 = (APlus x y)} {a2 = (AId k)} = Refl
optimizedPlusIsCorrect {a1 = (APlus x y)} {a2 = (APlus z w)} = Refl
optimizedPlusIsCorrect {a1 = (APlus x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusIsCorrect {a1 = (APlus x y)} {a2 = (AMult z w)} = Refl
optimizedPlusIsCorrect {st} {a1 = (AMinus x y)} {a2 = (ANum Z)} = rewrite plusZeroRightNeutral (minus (aeval st x) (aeval st y)) in Refl
optimizedPlusIsCorrect {a1 = (AMinus x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusIsCorrect {a1 = (AMinus x y)} {a2 = (AId k)} = Refl
optimizedPlusIsCorrect {a1 = (AMinus x y)} {a2 = (APlus z w)} = Refl
optimizedPlusIsCorrect {a1 = (AMinus x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusIsCorrect {a1 = (AMinus x y)} {a2 = (AMult z w)} = Refl
optimizedPlusIsCorrect {st} {a1 = (AMult x y)} {a2 = (ANum Z)} = rewrite plusZeroRightNeutral (mult (aeval st x) (aeval st y)) in Refl
optimizedPlusIsCorrect {a1 = (AMult x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusIsCorrect {a1 = (AMult x y)} {a2 = (AId k)} = Refl
optimizedPlusIsCorrect {a1 = (AMult x y)} {a2 = (APlus z w)} = Refl
optimizedPlusIsCorrect {a1 = (AMult x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusIsCorrect {a1 = (AMult x y)} {a2 = (AMult z w)} = Refl

optimizedMinus : AExp -> AExp -> AExp
optimizedMinus (ANum n) (ANum m) = ANum (n - m)
optimizedMinus (ANum Z) e = ANum Z
optimizedMinus e (ANum Z) = e
optimizedMinus e1 e2 = AMinus e1 e2

optimizedMult : AExp -> AExp -> AExp
optimizedMult (ANum n) (ANum m) = ANum (n * m)
optimizedMult (ANum Z) e = ANum Z
optimizedMult e (ANum Z) = ANum Z
optimizedMult (ANum (S Z)) e = e
optimizedMult e (ANum (S Z)) = e
optimizedMult e1 e2 = AMult e1 e2

constantFolding : AExp -> AExp
constantFolding (ANum k) = ANum k
constantFolding (AId x) = AId x
constantFolding (APlus e1 e2) = optimizedPlus (constantFolding e1) (constantFolding e2) 
constantFolding (AMinus e1 e2) = optimizedMinus (constantFolding e1) (constantFolding e2)
constantFolding (AMult e1 e2) = optimizedMult (constantFolding e1) (constantFolding e2)

partial
constantFoldingIsCorrect : aeval st a = aeval st (constantFolding a)
constantFoldingIsCorrect {st = st} {a = (ANum k)} = Refl
constantFoldingIsCorrect {st = st} {a = (AId k)} = Refl
-- plus
constantFoldingIsCorrect {st = st} {a = (APlus a1 a2)} =
  rewrite constantFoldingIsCorrect {st} {a=a1} in
  rewrite constantFoldingIsCorrect {st} {a=a2} in
  optimizedPlusIsCorrect {a1=constantFolding a1} {a2=constantFolding a2}
-- minus
constantFoldingIsCorrect {st = st} {a = (AMinus x y)} = ?constantFoldingIsCorrect_rhs_4
-- mult
constantFoldingIsCorrect {st = st} {a = (AMult x y)} = ?constantFoldingIsCorrect_rhs_5
