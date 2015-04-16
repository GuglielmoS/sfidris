module Induction

import Basics

%default total

andbTrueElim1 : (b : Bool) -> (c : Bool) -> andb b c = True -> b = True
andbTrueElim1 True c andbIsTrue = Refl
andbTrueElim1 False c andbIsTrue = andbIsTrue

andbTrueElim2 : (b : Bool) -> (c : Bool) -> andb b c = True -> c = True
andbTrueElim2 True True   _ = Refl
andbTrueElim2 True False  contra = contra
andbTrueElim2 False True  _ = Refl
andbTrueElim2 False False contra = contra

plusZeroRight : (n : Nat) -> n + 0 = n
plusZeroRight Z = Refl
plusZeroRight (S k) = cong (plusZeroRight k)

multZeroRight : (n : Nat) -> n * 0 = 0
multZeroRight Z = Refl
multZeroRight (S k) = multZeroRight k

plusN_Sm : (n : Nat) -> (m : Nat) -> S (n + m) = n + (S m)
plusN_Sm Z m = Refl
plusN_Sm (S k) m = rewrite plusN_Sm k m in Refl

plusComm : (n : Nat) -> (m : Nat) -> n + m = m + n
plusComm Z m = rewrite plusZeroRight m in Refl
plusComm (S k) m = rewrite sym $ plusN_Sm m k in cong $ plusComm k m

plusAssoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plusAssoc Z m p = Refl
plusAssoc (S k) m Z = rewrite plusZeroRight m in
                      rewrite plusZeroRight (plus k m) in Refl
plusAssoc (S k) Z (S j) = rewrite plusZeroRight k in Refl
plusAssoc (S k) (S i) (S j) = rewrite sym $ plusN_Sm i j in 
                              rewrite sym $ plusN_Sm k i in 
                              rewrite sym $ plusN_Sm k (S (plus i j)) in 
                              rewrite sym $ plusN_Sm k (plus i j) in
                              rewrite sym $ plusN_Sm (plus k i) j in
                              cong {f=S} $ cong {f=S} $ cong {f=S} $ plusAssoc k i j

double : Nat -> Nat
double Z = 0
double (S k) = S (S (double k)) 

doublePlus : (n : Nat) -> double n = n + n
doublePlus Z = Refl
doublePlus (S k) = rewrite sym $ plusN_Sm k k in 
                           cong {f=S} $ cong {f=S} $ doublePlus k 

bleNatRefl : (n : Nat) -> True = bleNat n n
bleNatRefl Z = Refl
bleNatRefl (S k) = bleNatRefl k 

zeroNBeqS : (n : Nat) -> beqNat 0 (S n) = False 
zeroNBeqS n = Refl

andbFalseRigth : (b : Bool) -> andb b False = False
andbFalseRigth False = Refl
andbFalseRigth True = Refl

plusBleCompatLeft : (n, m, p : Nat) -> bleNat n m = True -> bleNat (p + n) (p + m) = True
plusBleCompatLeft n m Z nEQm = nEQm
plusBleCompatLeft n m (S k) nEQm = rewrite plusBleCompatLeft n m k nEQm in Refl

succNotBeqZero : beqNat (S n) 0 = False
succNotBeqZero = Refl

multOneLeft : (n : Nat) -> 1 * n = n
multOneLeft = plusZeroRight 

all3Spec : (b, c : Bool) -> orb (andb b c) (orb (negb b) (negb c)) = True 
all3Spec False c = Refl
all3Spec True False = Refl
all3Spec True True = Refl

beqNatRefl : (n : Nat) -> True = beqNat n n
beqNatRefl Z = Refl
beqNatRefl (S k) = beqNatRefl k 
