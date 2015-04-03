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
  b_sum : Beautiful n -> Beautiful m -> Beautiful (n + m)

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

data Gorgeous : Nat -> Type where
  g_0     : Gorgeous 0
  g_plus3 : Gorgeous n -> Gorgeous (3+n)
  g_plus5 : Gorgeous n -> Gorgeous (5+n)

gorgeousPlus13 : Gorgeous n -> Gorgeous (13+n)
gorgeousPlus13 g_0          = g_plus5 (g_plus5 (g_plus3 g_0))
gorgeousPlus13 (g_plus3 n') = g_plus5 (g_plus5 (g_plus3 (g_plus3 n')))
gorgeousPlus13 (g_plus5 n') = g_plus3 (g_plus3 (g_plus3 (g_plus3 (g_plus3 (g_plus3 n')))))

gorgeousIsBeautiful : Gorgeous n -> Beautiful n
gorgeousIsBeautiful g_0          = b_0
gorgeousIsBeautiful (g_plus3 n') = b_sum b_3 (gorgeousIsBeautiful n') 
gorgeousIsBeautiful (g_plus5 n') = b_sum b_5 (gorgeousIsBeautiful n')

gorgeousSum : Gorgeous n -> Gorgeous m -> Gorgeous (n + m)
gorgeousSum g_0 mIsGorgeous = mIsGorgeous
gorgeousSum (g_plus3 nIsGorgeous) mIsGorgeous = g_plus3 (gorgeousSum nIsGorgeous mIsGorgeous)
gorgeousSum (g_plus5 nIsGorgeous) mIsGorgeous = g_plus5 (gorgeousSum nIsGorgeous mIsGorgeous)

evIsEven : Ev n -> even n
evIsEven ev_0            = Refl
evIsEven (ev_SS nIsEven) = evIsEven nIsEven

evSum : Ev n -> Ev m -> Ev (n + m)
evSum ev_0 mIsEven            = mIsEven
evSum (ev_SS nIsEven) mIsEven = ev_SS (evSum nIsEven mIsEven)
