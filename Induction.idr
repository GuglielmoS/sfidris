module Induction

import Basics

andbTrueElim1 : (b : Bool) -> (c : Bool) -> andb b c = True -> b = True
andbTrueElim1 True c andbIsTrue = Refl
andbTrueElim1 False c andbIsTrue = andbIsTrue

-- Exercise AndbTrueElim2

andbTrueElim2 : (b : Bool) -> (c : Bool) -> andb b c = True -> c = True
andbTrueElim2 True True   _ = Refl
andbTrueElim2 True False  contra = contra
andbTrueElim2 False True  _ = Refl
andbTrueElim2 False False contra = contra

-- Exercise End

plusZeroRight : (n : Nat) -> n + 0 = n
plusZeroRight Z = Refl
plusZeroRight (S k) = cong (plusZeroRight k)

-- Exercise BASIC_INDUCTION

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

-- Exercise End

-- Exercise Double_Plus

double : Nat -> Nat
double Z = 0
double (S k) = S (S (double k)) 

doublePlus : (n : Nat) -> double n = n + n
doublePlus Z = Refl
doublePlus (S k) = rewrite sym $ plusN_Sm k k in 
                           cong {f=S} $ cong {f=S} $ doublePlus k 

-- Exercise End
