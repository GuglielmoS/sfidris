module Logic

import Basics
import Induction 

%default total

-- Conjunction

infixl 8 /\
data (/\) : Type -> Type -> Type where
  conj : {P, Q : Type} -> P -> Q -> P /\ Q

andExample : (0 = 0) /\ (4 = 2 * 2)
andExample = conj Refl Refl 

proj1 : {P, Q : Type} -> P /\ Q -> P
proj1 (conj P Q) = P

proj2 : {P, Q : Type} -> P /\ Q -> Q
proj2 (conj P Q) = Q

andCommute : {P, Q : Type} -> P /\ Q -> Q /\ P
andCommute (conj P Q) = conj Q P

andAssoc : {P, Q, R : Type} -> P /\ (Q /\ R) -> (P /\ Q) /\ R 
andAssoc (conj P (conj Q R)) = conj (conj P Q) R

-- If And Only If

(<->) : Type -> Type -> Type
(<->) p q = (p -> q) /\ (q -> p)

iffImplies : {P, Q : Type} -> (P <-> Q) -> P -> Q
iffImplies (conj pit itp) p = pit p

iffRefl : {P : Type} -> P <-> P
iffRefl = conj id id 

iffSym : {P, Q : Type} -> (P <-> Q) -> (Q <-> P)
iffSym (conj pq qp) = conj qp pq 

iffTrans : {P, Q, R : Type} -> (P <-> Q) -> (Q <-> R) -> (P <-> R)
iffTrans (conj pq qp) (conj qr rq) = conj (qr . pq) (qp . rq)

-- Disjuction

infixl 7 \/
data (\/) : Type -> Type -> Type where
  orIntroL : {P, Q : Type} -> P -> P \/ Q
  orIntroR : {P, Q : Type} -> Q -> P \/ Q

orCommute : {P, Q : Type} -> P \/ Q -> Q \/ P
orCommute (orIntroL P) = orIntroR P
orCommute (orIntroR Q) = orIntroL Q

orDistributesOverAnd1 : {P, Q, R : Type} -> P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R)
orDistributesOverAnd1 (orIntroL p) = conj (orIntroL p) (orIntroL p)
orDistributesOverAnd1 (orIntroR (conj q r)) = conj (orIntroR q) (orIntroR r)

orDistributesOverAnd2 : {P, Q, R : Type} -> (P \/ Q) /\ (P \/ R) ->  P \/ (Q /\ R)
orDistributesOverAnd2 (conj (orIntroL _) (orIntroL p)) = orIntroL p
orDistributesOverAnd2 (conj (orIntroL p) (orIntroR _)) = orIntroL p
orDistributesOverAnd2 (conj (orIntroR _) (orIntroL p)) = orIntroL p
orDistributesOverAnd2 (conj (orIntroR q) (orIntroR r)) = orIntroR (conj q r)

orDistributesOverAnd : {P, Q, R : Type} -> P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) 
orDistributesOverAnd = conj orDistributesOverAnd1 orDistributesOverAnd2

andbProp : (b, c : Bool) -> andb b c = True -> (b = True) /\ (c = True)
andbProp False False prf = conj prf prf
andbProp False True prf = conj prf Refl
andbProp True c prf = conj Refl prf

andbTrueIntro : (b, c : Bool) -> ((b = True) /\ (c = True)) -> andb b c = True 
andbTrueIntro b c (conj bTrue cTrue) = rewrite bTrue in rewrite cTrue in Refl

andbFalse : (b, c : Bool) -> andb b c = False -> ((b = False) \/ (c = False))
andbFalse False c prf = orIntroL Refl
andbFalse True c prf = rewrite prf in (orIntroR Refl)

orbProp : (b, c : Bool) -> orb b c = True -> ((b = True) \/ (c = True))
orbProp False c prf = rewrite prf in orIntroR Refl
orbProp True c prf = orIntroL Refl

orbFalseElim : (b, c : Bool) -> orb b c = False -> ((b = False) /\ (c = False))
orbFalseElim False c prf = conj Refl prf
orbFalseElim True False prf = conj prf Refl
orbFalseElim True True prf = conj prf prf

-- Falsehood & Negation

neg : Type -> Type
neg p = p -> Void

exFalsoQuodlibet : {P : Type} -> Void -> P
exFalsoQuodlibet = void

notFalse : neg Void
notFalse false = false

contradictionImpliesAnything : (P, Q : Type) -> (P /\ (neg P)) -> Q
contradictionImpliesAnything P Q (conj p notP) = exFalsoQuodlibet (notP p)

doubleNeg : {P : Type} -> (P -> neg (neg P))
doubleNeg p notP = notP p

-- Inequality

notFalseThenTrue : (b : Bool) -> (neg (b = False)) -> b = True 
notFalseThenTrue False prf = exFalsoQuodlibet (prf Refl)
notFalseThenTrue True _ = Refl

succInjectiveNEQ : (n, m : Nat) -> (neg (S n = S m)) -> (neg (n = m))
succInjectiveNEQ n m snNEQsm nNEQm = snNEQsm (cong nNEQm)

falseBeqNat : (n, m : Nat) -> (neg (n = m)) -> beqNat n m = False
falseBeqNat Z      Z      prf = exFalsoQuodlibet (prf Refl)
falseBeqNat Z      (S _)  _   = Refl
falseBeqNat (S _)  Z      _   = Refl
falseBeqNat (S n') (S m') prf = falseBeqNat n' m' (succInjectiveNEQ n' m' prf)
