module Imp

import Logic

%default total

Id : Type
Id = Nat

State : Type
State = Id -> Nat

emptyState : State
emptyState id = 0

update : State -> Id -> Nat -> State
update st x n = \x' => if x == x' then n else st x'

%elim
data AExp : Type where
  ANum : Nat -> AExp
  AId : Id -> AExp
  APlus : AExp -> AExp -> AExp
  AMinus : AExp -> AExp -> AExp
  AMult : AExp -> AExp -> AExp

%elim
data BExp : Type where
  BTrue : BExp
  BFalse : BExp
  BEq : AExp -> AExp -> BExp
  BLe : AExp -> AExp -> BExp
  BNot : BExp -> BExp
  BAnd : BExp -> BExp -> BExp

data Com : Type where
  CSkip : Com
  CAss : Id -> AExp -> Com
  CSeq : Com -> Com -> Com
  CIf : BExp -> Com -> Com -> Com
  CWhile : BExp -> Com -> Com

aeval : State -> AExp -> Nat
aeval st (ANum n) = n
aeval st (AId x) = st x
aeval st (APlus a1 a2) = aeval st a1 + aeval st a2
aeval st (AMinus a1 a2) = aeval st a1 - aeval st a2
aeval st (AMult a1 a2) = aeval st a1 * aeval st a2

beval : State -> BExp -> Bool
beval st BTrue = True 
beval st BFalse = False
beval st (BEq a1 a2) = aeval st a1 == aeval st a2
beval st (BLe a1 a2) = aeval st a1 <= aeval st a2
beval st (BNot b1) = not (beval st b1)
beval st (BAnd b1 b2) = beval st b1 && beval st b2

data ceval : Com -> State -> State -> Type where
  E_SKip : ceval CSkip st st
  E_Ass : aeval st a1 = n -> ceval (CAss x a1) st (update st x n) 
  E_Seq : ceval c1 st st' -> ceval c2 st' st'' -> ceval (CSeq c1 c2) st st''
  E_IfTrue : beval st b = True -> ceval c1 st st' -> ceval (CIf b c1 c2) st st' 
  E_IfFalse : beval st b = False -> ceval c2 st st' -> ceval (CIf b c1 c2) st st' 
  E_WhileEnd : beval st b = False -> ceval (CWhile b c) st st
  E_WhileLoop : beval st b = True 
                -> ceval c st st' 
                -> ceval (CWhile b c) st' st''
                -> ceval (CWhile b c) st st''

{- Evaluation as a relation (without variables, thus without state)
data AEvalR : AExp -> Nat -> Type where
  E_ANum : AEvalR (ANum n) n
  E_APlus : AEvalR e1 n1 -> AEvalR e2 n2 -> AEvalR (APlus e1 e2) (n1 + n2)
  E_AMinus : AEvalR e1 n1 -> AEvalR e2 n2 -> AEvalR (AMinus e1 e2) (n1 - n2)
  E_AMult : AEvalR e1 n1 -> AEvalR e2 n2 -> AEvalR (AMult e1 e2) (n1 * n2)

aeval_iff_AEvalR_left : AEvalR a n -> aeval st a = n
aeval_iff_AEvalR_left E_ANum = Refl
aeval_iff_AEvalR_left {st} (E_APlus x y) = rewrite aeval_iff_AEvalR_left {st} x in
                                           rewrite aeval_iff_AEvalR_left {st} y in Refl
aeval_iff_AEvalR_left {st} (E_AMinus x y) = rewrite aeval_iff_AEvalR_left {st} x in
                                            rewrite aeval_iff_AEvalR_left {st} y in Refl
aeval_iff_AEvalR_left {st} (E_AMult x y) = rewrite aeval_iff_AEvalR_left {st} x in
                                           rewrite aeval_iff_AEvalR_left {st} y in Refl

aeval_iff_AEvalR_right : (aeval st a = n) -> AEvalR a n
aeval_iff_AEvalR_right prf {a = (ANum k)} = rewrite sym prf in E_ANum
aeval_iff_AEvalR_right prf {a = (APlus x y)} = rewrite sym prf in 
                                               (E_APlus (aeval_iff_AEvalR_right Refl) (aeval_iff_AEvalR_right Refl))
aeval_iff_AEvalR_right prf {a = (AMinus x y)} = rewrite sym prf in
                                                E_AMinus (aeval_iff_AEvalR_right Refl) (aeval_iff_AEvalR_right Refl)
aeval_iff_AEvalR_right prf {a = (AMult x y)} = rewrite sym prf in 
                                               E_AMult (aeval_iff_AEvalR_right Refl) (aeval_iff_AEvalR_right Refl)
aeval_iff_AEvalR : (AEvalR a n) <-> (aeval st a = n)
aeval_iff_AEvalR = conj aeval_iff_AEvalR_left aeval_iff_AEvalR_right
-}

-- Trivial constant folding
optimizeZeroPlus : AExp -> AExp
optimizeZeroPlus (ANum n) = ANum n
optimizeZeroPlus (AId x) = AId x
optimizeZeroPlus (APlus (ANum Z) e2) = optimizeZeroPlus e2
optimizeZeroPlus (APlus e1 e2) = APlus (optimizeZeroPlus e1) (optimizeZeroPlus e2)
optimizeZeroPlus (AMinus e1 e2) = AMinus (optimizeZeroPlus e1) (optimizeZeroPlus e2)
optimizeZeroPlus (AMult e1 e2) = AMult (optimizeZeroPlus e1) (optimizeZeroPlus e2)

optimizeZeroPlusSound : aeval st (optimizeZeroPlus a) = aeval st a
optimizeZeroPlusSound {st} {a = (ANum _)} = Refl
optimizeZeroPlusSound {st} {a = (AId x)} = Refl
optimizeZeroPlusSound {st} {a = (APlus (ANum Z) e2)} = optimizeZeroPlusSound {a=e2}
optimizeZeroPlusSound {st} {a = (APlus (ANum (S _)) e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (APlus (AId _) e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (APlus e1@(APlus _ _) e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e1} in
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (APlus e1@(AMinus _ _) e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e1} in
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (APlus e1@(AMult _ _) e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e1} in
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (AMinus e1 e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e1} in
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl
optimizeZeroPlusSound {st} {a = (AMult e1 e2)} =
  rewrite optimizeZeroPlusSound {st} {a=e1} in
  rewrite optimizeZeroPlusSound {st} {a=e2} in Refl

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
