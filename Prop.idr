module Prop

import Basics
import Logic

even : Nat -> Type
even n = (evenb n = True)

data Ev : Nat -> Type where
  ev_0  : Ev 0
  ev_SS : {n : Nat} -> Ev n -> Ev (S (S n))

double : Nat -> Nat
double n = n + n

doubleEven : {n : Nat} -> Ev (double n)
doubleEven {n = Z}     = ev_0
doubleEven {n = (S k)} = rewrite sym $ plusSuccRightSucc k k in (ev_SS doubleEven)

data Beautiful : Nat -> Type where
  b_0   : Beautiful 0
  b_3   : Beautiful 3
  b_5   : Beautiful 5
  b_sum : {n, m : Nat} -> Beautiful n -> Beautiful m -> Beautiful (n + m)

threeIsBeautiful : Beautiful 3
threeIsBeautiful = b_3

eightIsBeautiful : Beautiful 8
eightIsBeautiful = b_sum b_3 b_5

eightIsBeautiful' : Beautiful 8
eightIsBeautiful' = b_sum b_0 (b_sum b_3 b_5)

eightIsBeautiful'' : Beautiful 8
eightIsBeautiful'' = b_sum b_0 (b_sum b_0 (b_sum b_3 b_5))

eightIsBeautiful''' : Beautiful 8
eightIsBeautiful''' = b_sum b_0 (b_sum b_0 (b_sum b_0 (b_sum b_3 b_5)))
-- ...

beautifulPlusEight : {n : Nat} -> Beautiful n -> Beautiful (8+n)
beautifulPlusEight nIsBeautiful = b_sum eightIsBeautiful nIsBeautiful

beautifulTimes2 : {n : Nat} -> Beautiful n -> Beautiful (2*n)
beautifulTimes2 {n} nIsBeautiful = rewrite plusZeroRightNeutral n in (b_sum nIsBeautiful nIsBeautiful)
