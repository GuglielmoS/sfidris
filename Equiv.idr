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
