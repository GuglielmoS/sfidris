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
-- CONSTANT FOLDING (from SF)
-- Currently not completely proved
--

foldConstantsAExp : AExp -> AExp
foldConstantsAExp (ANum n) = ANum n
foldConstantsAExp (AId i) = AId i
foldConstantsAExp (APlus a1 a2) = 
  case (foldConstantsAExp a1, foldConstantsAExp a2) of
       (ANum n1, ANum n2) => ANum (n1 + n2)
       (a1', a2')         => APlus a1' a2'
foldConstantsAExp (AMinus a1 a2) =
  case (foldConstantsAExp a1, foldConstantsAExp a2) of
       (ANum n1, ANum n2) => ANum (n1 - n2)
       (a1', a2')         => AMinus a1' a2'
foldConstantsAExp (AMult a1 a2) = 
  case (foldConstantsAExp a1, foldConstantsAExp a2) of
       (ANum n1, ANum n2) => ANum (n1 * n2)
       (a1', a2')         => AMult a1' a2'

partial
foldConstantsAExpSound : aequiv {st} a (foldConstantsAExp a)
foldConstantsAExpSound {a = (ANum _)} = Refl
foldConstantsAExpSound {a = (AId _)} = Refl
-- plus
foldConstantsAExpSound {a = (APlus (ANum _) (ANum _))} = Refl
foldConstantsAExpSound {a = (APlus (ANum n) a2)} {st} = ?foldConstantsAExpSound_operationsProof
foldConstantsAExpSound {a = (APlus (AId _) a2)} {st} = rewrite foldConstantsAExpSound {st} {a=a2} in Refl
foldConstantsAExpSound {a = (APlus (APlus _ _) a2)} {st} = ?boh1
foldConstantsAExpSound {a = (APlus (AMinus _ _) a2)} {st} = ?boh2
foldConstantsAExpSound {a = (APlus (AMult _ _) a2)} {st} = ?boh3 
-- minus
foldConstantsAExpSound {a = (AMinus (ANum _) (ANum _))} = Refl
foldConstantsAExpSound {a = (AMinus (ANum n) a2)} {st} = ?foldConstantsAExpSound_operationsProof
foldConstantsAExpSound {a = (AMinus (APlus _ _) a2)} {st} = ?boh12
foldConstantsAExpSound {a = (AMinus (AMinus _ _) a2)} {st} = ?boh22
foldConstantsAExpSound {a = (AMinus (AMult _ _) a2)} {st} = ?boh32
-- mult
foldConstantsAExpSound {a = (AMult (ANum _) (ANum _))} = Refl
foldConstantsAExpSound {a = (AMult (ANum n) a2)} {st} = ?foldConstantsAExpSound_operationsProof
foldConstantsAExpSound {a = (AMult (APlus _ _) a2)} {st} = ?boh123
foldConstantsAExpSound {a = (AMult (AMinus _ _) a2)} {st} = ?boh223
foldConstantsAExpSound {a = (AMult (AMult _ _) a2)} {st} = ?boh323

-- Proofs

Equiv.foldConstantsAExpSound_operationsProof = proof
  intros
  let IHa2 = foldConstantsAExpSound {st} {a=a2}
  rewrite sym IHa2
  induction (foldConstantsAExp a2)
  intros
  compute
  trivial
  intros
  compute
  trivial
  intros
  compute
  trivial
  intros
  compute
  trivial
  intros
  compute
  trivial

--
-- CONSTANTS FOLDING (another variant)
--

optimizedPlus : AExp -> AExp -> AExp
optimizedPlus (ANum n) (ANum m) = ANum (n + m)
optimizedPlus (ANum Z) e = e
optimizedPlus e (ANum Z) = e
optimizedPlus e1 e2 = APlus e1 e2

optimizedPlusSound : {a1, a2 : AExp} -> {st : State} -> 
  plus (aeval st a1) (aeval st a2) = aeval st (optimizedPlus a1 a2) 
optimizedPlusSound {a1 = (ANum k)} {a2 = (ANum j)} = Refl
optimizedPlusSound {a1 = (ANum Z)} {a2 = (AId j)} = Refl
optimizedPlusSound {a1 = (ANum (S k))} {a2 = (AId j)} = Refl
optimizedPlusSound {a1 = (ANum Z)} {a2 = (APlus x y)} = Refl
optimizedPlusSound {a1 = (ANum (S k))} {a2 = (APlus x y)} = Refl
optimizedPlusSound {a1 = (ANum Z)} {a2 = (AMinus x y)} = Refl
optimizedPlusSound {a1 = (ANum (S k))} {a2 = (AMinus x y)} = Refl
optimizedPlusSound {a1 = (ANum Z)} {a2 = (AMult x y)} = Refl
optimizedPlusSound {a1 = (ANum (S k))} {a2 = (AMult x y)} = Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (ANum Z)} {st} =
  rewrite plusZeroRightNeutral (st k) in Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (ANum (S j))} = Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (AId j)} = Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (APlus x y)} = Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (AMinus x y)} = Refl
optimizedPlusSound {a1 = (AId k)} {a2 = (AMult x y)} = Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (ANum Z)} {st} =
  rewrite plusZeroRightNeutral (plus (aeval st x) (aeval st y)) in Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (AId k)} = Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (APlus z w)} = Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusSound {a1 = (APlus x y)} {a2 = (AMult z w)} = Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (ANum Z)} {st} =
  rewrite plusZeroRightNeutral (minus (aeval st x) (aeval st y)) in Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (AId k)} = Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (APlus z w)} = Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusSound {a1 = (AMinus x y)} {a2 = (AMult z w)} = Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (ANum Z)} {st} =
  rewrite plusZeroRightNeutral (mult (aeval st x) (aeval st y)) in Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (ANum (S k))} = Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (AId k)} = Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (APlus z w)} = Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (AMinus z w)} = Refl
optimizedPlusSound {a1 = (AMult x y)} {a2 = (AMult z w)} = Refl

optimizedMinus : AExp -> AExp -> AExp
optimizedMinus (ANum n) (ANum m) = ANum (n - m)
optimizedMinus (ANum Z) e = ANum Z
optimizedMinus e (ANum Z) = e
optimizedMinus e1 e2 = AMinus e1 e2

optimizedMinusSound : {a1, a2 : AExp} -> {st : State} -> 
  (aeval st a1) - (aeval st a2) = aeval st (optimizedMinus a1 a2) 
optimizedMinusSound {a1 = (ANum k)} {a2 = (ANum j)} = Refl
optimizedMinusSound {a1 = (ANum Z)} {a2 = (AId j)} = Refl
optimizedMinusSound {a1 = (ANum (S k))} {a2 = (AId j)} = Refl
optimizedMinusSound {a1 = (ANum Z)} {a2 = (APlus x y)} = Refl
optimizedMinusSound {a1 = (ANum (S k))} {a2 = (APlus x y)} = Refl
optimizedMinusSound {a1 = (ANum Z)} {a2 = (AMinus x y)} = Refl
optimizedMinusSound {a1 = (ANum (S k))} {a2 = (AMinus x y)} = Refl
optimizedMinusSound {a1 = (ANum Z)} {a2 = (AMult x y)} = Refl
optimizedMinusSound {a1 = (ANum (S k))} {a2 = (AMult x y)} = Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (ANum Z)} {st} = 
  rewrite minusZeroRight (st k) in Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (ANum (S j))} = Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (AId j)} = Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (APlus x y)} = Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (AMinus x y)} = Refl
optimizedMinusSound {a1 = (AId k)} {a2 = (AMult x y)} = Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (ANum Z)} {st} = 
  rewrite minusZeroRight (plus (aeval st x) (aeval st y)) in Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (ANum (S k))} = Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (AId k)} = Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (APlus z w)} = Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (AMinus z w)} = Refl
optimizedMinusSound {a1 = (APlus x y)} {a2 = (AMult z w)} = Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (ANum Z)} {st} = 
  rewrite minusZeroRight (minus (aeval st x) (aeval st y)) in Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (ANum (S k))} = Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (AId k)} = Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (APlus z w)} = Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (AMinus z w)} = Refl
optimizedMinusSound {a1 = (AMinus x y)} {a2 = (AMult z w)} = Refl
optimizedMinusSound {st} {a1 = (AMult x y)} {a2 = (ANum Z)} = 
  rewrite minusZeroRight (mult (aeval st x) (aeval st y)) in Refl
optimizedMinusSound {a1 = (AMult x y)} {a2 = (ANum (S k))} = Refl
optimizedMinusSound {a1 = (AMult x y)} {a2 = (AId k)} = Refl
optimizedMinusSound {a1 = (AMult x y)} {a2 = (APlus z w)} = Refl
optimizedMinusSound {a1 = (AMult x y)} {a2 = (AMinus z w)} = Refl
optimizedMinusSound {a1 = (AMult x y)} {a2 = (AMult z w)} = Refl

optimizedMult : AExp -> AExp -> AExp
optimizedMult (ANum n) (ANum m) = ANum (n * m)
optimizedMult (ANum Z) e = ANum Z
optimizedMult e (ANum Z) = ANum Z
optimizedMult e1 e2 = AMult e1 e2

optimizedMultSound : {a1, a2 : AExp} -> {st : State} -> 
  (aeval st a1) * (aeval st a2) = aeval st (optimizedMult a1 a2) 
optimizedMultSound {a1 = (ANum k)} {a2 = (ANum j)} = Refl
optimizedMultSound {a1 = (ANum Z)} {a2 = (AId j)} = Refl
optimizedMultSound {a1 = (ANum (S k))} {a2 = (AId j)} = Refl
optimizedMultSound {a1 = (ANum Z)} {a2 = (APlus x y)} = Refl
optimizedMultSound {a1 = (ANum (S k))} {a2 = (APlus x y)} = Refl
optimizedMultSound {a1 = (ANum Z)} {a2 = (AMinus x y)} = Refl
optimizedMultSound {a1 = (ANum (S k))} {a2 = (AMinus x y)} = Refl
optimizedMultSound {a1 = (ANum Z)} {a2 = (AMult x y)} = Refl
optimizedMultSound {a1 = (ANum (S k))} {a2 = (AMult x y)} = Refl
optimizedMultSound {a1 = (AId k)} {a2 = (ANum Z)} {st} = 
  rewrite multZeroRightZero (st k) in Refl
optimizedMultSound {a1 = (AId k)} {a2 = (ANum (S j))} = Refl
optimizedMultSound {a1 = (AId k)} {a2 = (AId j)} = Refl
optimizedMultSound {a1 = (AId k)} {a2 = (APlus x y)} = Refl
optimizedMultSound {a1 = (AId k)} {a2 = (AMinus x y)} = Refl
optimizedMultSound {a1 = (AId k)} {a2 = (AMult x y)} = Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (ANum Z)} {st} = 
  rewrite multZeroRightZero (plus (aeval st x) (aeval st y)) in Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (ANum (S k))} = Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (AId k)} = Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (APlus z w)} = Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (AMinus z w)} = Refl
optimizedMultSound {a1 = (APlus x y)} {a2 = (AMult z w)} = Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (ANum Z)} {st} = 
  rewrite multZeroRightZero (minus (aeval st x) (aeval st y)) in Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (ANum (S k))} = Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (AId k)} = Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (APlus z w)} = Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (AMinus z w)} = Refl
optimizedMultSound {a1 = (AMinus x y)} {a2 = (AMult z w)} = Refl
optimizedMultSound {st} {a1 = (AMult x y)} {a2 = (ANum Z)} = 
  rewrite multZeroRightZero (mult (aeval st x) (aeval st y)) in Refl
optimizedMultSound {a1 = (AMult x y)} {a2 = (ANum (S k))} = Refl
optimizedMultSound {a1 = (AMult x y)} {a2 = (AId k)} = Refl
optimizedMultSound {a1 = (AMult x y)} {a2 = (APlus z w)} = Refl
optimizedMultSound {a1 = (AMult x y)} {a2 = (AMinus z w)} = Refl
optimizedMultSound {a1 = (AMult x y)} {a2 = (AMult z w)} = Refl

constantsFolding : AExp -> AExp
constantsFolding (ANum k) = ANum k
constantsFolding (AId x) = AId x
constantsFolding (APlus e1 e2) = optimizedPlus (constantsFolding e1) (constantsFolding e2) 
constantsFolding (AMinus e1 e2) = optimizedMinus (constantsFolding e1) (constantsFolding e2)
constantsFolding (AMult e1 e2) = optimizedMult (constantsFolding e1) (constantsFolding e2)

constantsFoldingSound : aeval st a = aeval st (constantsFolding a)
constantsFoldingSound {st = st} {a = (ANum k)} = Refl
constantsFoldingSound {st = st} {a = (AId k)} = Refl
constantsFoldingSound {st = st} {a = (APlus a1 a2)} =
  rewrite constantsFoldingSound {st} {a=a1} in
  rewrite constantsFoldingSound {st} {a=a2} in
  optimizedPlusSound {a1=constantsFolding a1} {a2=constantsFolding a2}
constantsFoldingSound {st = st} {a = (AMinus a1 a2)} = 
  rewrite constantsFoldingSound {st} {a=a1} in
  rewrite constantsFoldingSound {st} {a=a2} in
  optimizedMinusSound {a1=constantsFolding a1} {a2=constantsFolding a2}
constantsFoldingSound {st = st} {a = (AMult a1 a2)} =
  rewrite constantsFoldingSound {st} {a=a1} in
  rewrite constantsFoldingSound {st} {a=a2} in
  optimizedMultSound {a1=constantsFolding a1} {a2=constantsFolding a2}
