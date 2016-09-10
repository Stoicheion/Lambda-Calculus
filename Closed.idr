module Closed

import Data.Fin

mutual
  data Open :  Nat -> Type where
    Ref : Fin maxBV -> Open maxBV
    More : Close maxBV -> Open maxBV
  data Close : Nat -> Type where
    Lam : Open (S maxBV) -> Close maxBV
    App : Close maxBV -> Close maxBV -> Close maxBV

Closed : Type
Closed = Close 0

id : Closed
id = Lam (Ref FZ)
true : Closed
true = Lam (More (Lam (Ref FZ)))
false : Closed
false = Lam (More (Lam (Ref (FS FZ))))

--Decrease the number in the type of these two terms and it will fail to compile.
open1 : Close 1
open1 = Lam (Ref (FS FZ))
open2 : Close 2
open2 = Lam (Ref (FS (FS FZ)))
