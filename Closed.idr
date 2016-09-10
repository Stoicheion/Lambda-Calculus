module Closed

import Data.Fin

data Term : {default 0 abs : Nat} -> Type where
  Ref : Fin maxBV -> Term {abs = maxBV}
  Lam : Term {abs = S maxBV} -> Term {abs = maxBV}
  App : Term {abs = maxBV} -> Term {abs = maxBV} -> Term {abs = maxBV}

Closed : Type
Closed = Term

id : Closed
id = Lam (Ref FZ)
true : Closed
true = Lam (Lam (Ref FZ))
false : Closed
false = Lam (Lam (Ref (FS FZ)))
U : Closed
U = Lam (App (Ref FZ) (Ref FZ))

--Decrease the number in the type of these three terms and it will fail to compile.
open0 : Term {abs = 1}
open0 = Ref FZ
open1 : Term {abs = 1}
open1 = Lam (Ref (FS FZ))
open2 : Term {abs = 2}
open2 = Lam (Ref (FS (FS FZ)))
