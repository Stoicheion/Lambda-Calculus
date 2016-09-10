module Closed

import Data.Fin

data Close : Nat -> Type where
  Ref : Fin maxBV -> Close maxBV
  Lam : Close (S maxBV) -> Close maxBV
  App : Close maxBV -> Close maxBV -> Close maxBV

Closed : Type
Closed = Close 0

id : Closed
id = Lam (Ref FZ)
true : Closed
true = Lam (Lam (Ref FZ))
false : Closed
false = Lam (Lam (Ref (FS FZ)))
U : Closed
U = Lam (App (Ref FZ) (Ref FZ))

--Decrease the number in the type of these three terms and it will fail to compile.
open0 : Close 1
open0 = Ref FZ
open1 : Close 1
open1 = Lam (Ref (FS FZ))
open2 : Close 2
open2 = Lam (Ref (FS (FS FZ)))
