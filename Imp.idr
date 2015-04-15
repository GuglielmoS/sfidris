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

%elim
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
-- Determinism of evaluation
--

cevalDeterministic : ceval c st st1 -> ceval c st st2 -> st1 = st2
cevalDeterministic E_SKip E_SKip = Refl
-- assignment
cevalDeterministic (E_Ass prf) (E_Ass prf1) = ?assignProof
-- sequence
cevalDeterministic (E_Seq _ c2) (E_Seq _ c2') = ?seqProof
-- if
cevalDeterministic (E_IfTrue _ x) (E_IfTrue _ z) = cevalDeterministic x z
cevalDeterministic (E_IfTrue prf bodyEval) (E_IfFalse prf' bodyEval') = ?ifContraProof_1
cevalDeterministic (E_IfFalse _ x) (E_IfFalse _ z) = cevalDeterministic x z
cevalDeterministic (E_IfFalse prf x) (E_IfTrue y z) = ?ifContraProof_2
-- while
cevalDeterministic (E_WhileEnd _) (E_WhileEnd _) = Refl
cevalDeterministic (E_WhileLoop prf x y) (E_WhileLoop z w s) = ?whileLoopProof
cevalDeterministic (E_WhileEnd prf) (E_WhileLoop x y z) = ?whileContraProof_1
cevalDeterministic (E_WhileLoop prf x y) (E_WhileEnd z) = ?whileContraProof_2

-- Proofs

Imp.assignProof = proof
  intro st
  intro a1
  intro n
  intro a1Eval
  intro n'
  rewrite sym a1Eval
  intro nEQn'
  intro x
  rewrite nEQn'
  trivial

Imp.seqProof = proof
  intro st1
  intro st'
  intro c2
  intro c2Eval
  intro st2
  intro st'1
  intro c2Eval''
  intro st
  intro c1
  intro c1Eval
  intro c1Eval'
  let st'EQst'1 = cevalDeterministic c1Eval c1Eval'
  let c2Eval' = replace st'EQst'1 {P = \s => ceval c2 s st1} c2Eval
  exact cevalDeterministic c2Eval' c2Eval''

Imp.ifContraProof_1 = proof
  intro st
  intro b
  intro prf
  intro st1
  intro c1
  intro bodyEval
  rewrite sym prf
  exact (void . trueNotFalse)

Imp.ifContraProof_2 = proof
  intro st
  intro b
  intro prf
  intro st1
  intro c2
  intro bodyEval
  rewrite sym prf
  intro contra
  exact void $ trueNotFalse (sym contra)

Imp.whileLoopProof = proof
  intro st
  intro b
  intro prf
  intro c
  intro st'
  intro cEval
  intro st1
  intro whileEval
  intro prf'
  intro st'1
  intro cEval'
  intro st2
  let stEQst'1 = cevalDeterministic cEval cEval'
  rewrite stEQst'1
  intro whileEval'
  exact cevalDeterministic whileEval whileEval'

Imp.whileContraProof_1 = proof
  intro st
  intro b
  intro bIsFalse
  rewrite sym bIsFalse
  intro contra
  exact void $ trueNotFalse (sym contra)

Imp.whileContraProof_2 = proof
  intro st
  intro b
  intro bIsTrue
  intro c
  intro st'
  intro bodyEval
  intro st1
  intro whileEval
  rewrite sym bIsTrue
  exact void . trueNotFalse
