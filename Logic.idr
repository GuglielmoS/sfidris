module Logic

import Basics
import Induction 

-- Conjunction

data And : Type -> Type -> Type where
  conj : {P,Q : Type} -> P -> Q -> And P Q

syntax [P] "/\\" [Q] = And P Q

andExample : And (0 = 0) (4 = 2 * 2)
andExample = conj Refl Refl 

proj1 : {P, Q : Type} -> (P /\ Q) -> P
proj1 (conj P Q) = P

proj2 : {P, Q : Type} -> (P /\ Q) -> Q
proj2 (conj P Q) = Q

andCommute : {P, Q : Type} -> (P /\ Q) -> (Q /\ P)
andCommute (conj P Q) = conj Q P

andAssoc : {P, Q, R : Type} -> (P /\ (Q /\ R)) -> (P /\ Q) /\ R 
andAssoc (conj P (conj Q R)) = conj (conj P Q) R

-- If And Only If

iffImplies : {P, Q : Type} -> ((P -> Q) /\ (Q -> P)) -> P -> Q
iffImplies (conj l r) p = (l p)

iffRefl : {P : Type} -> ((P -> P) /\ (P -> P))
iffRefl = conj id id 

iffSym : {P, Q : Type} -> ((P -> Q) /\ (Q -> P)) -> ((Q -> P) /\ (P -> Q))
iffSym (conj pq qp) = conj qp pq

iffTrans : {P, Q, R : Type} -> ((P -> Q) /\ (Q -> P)) -> ((Q -> R) /\ (R -> Q)) ->
                               ((P -> R) /\ (R -> P))
iffTrans (conj pq qp) (conj qr rq) = conj (qr . pq) (qp . rq)

-- Disjuction

data Or : Type -> Type -> Type where
  orIntroL : {P, Q : Type} -> P -> Or P Q
  orIntroR : {P, Q : Type} -> Q -> Or P Q

syntax [P] "\\/" [Q] = Or P Q

orCommute : {P, Q : Type} -> (P \/ Q) -> (Q \/ P)
orCommute (orIntroL P) = orIntroR P
orCommute (orIntroR Q) = orIntroL Q

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

-- Falsehood

exFalsoQuodlibet : {P : Type} -> Void -> P
exFalsoQuodlibet = void

notFalse : Void -> Void
notFalse false = false

contradictionImpliesAnything : (P, Q : Type) -> (P /\ (P -> Void)) -> Q
contradictionImpliesAnything P Q (conj p notP) = exFalsoQuodlibet (notP p)

-- Inequality

notFalseThenTrue : (b : Bool) -> (b = False -> Void) -> b = True 
notFalseThenTrue False prf = exFalsoQuodlibet (prf Refl)
notFalseThenTrue True _ = Refl

succInjectiveNEQ : (n, m : Nat) -> (S n = S m -> Void) -> (n = m -> Void)
succInjectiveNEQ n m snNEQsm nNEQm = snNEQsm (cong nNEQm)

falseBeqNat : (n, m : Nat) -> (n = m -> Void) -> beqNat n m = False
falseBeqNat Z      Z      prf = exFalsoQuodlibet (prf Refl)
falseBeqNat Z      (S _)  _   = Refl
falseBeqNat (S _)  Z      _   = Refl
falseBeqNat (S n') (S m') prf = falseBeqNat n' m' (succInjectiveNEQ n' m' prf)
