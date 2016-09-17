module Lambda


import public Data.Fin

public export
data Term : {default 0 abs : Nat} -> Type where
  Ref : Fin maxBV -> Term {abs = maxBV}
  Lam : Term {abs = S maxBV} -> Term {abs = maxBV}
  App : Term {abs = maxBV} -> Term {abs = maxBV} -> Term {abs = maxBV}

%name Term t, u, s, p, q, r
%name Fin  n, m, k

public export
Closed : Type
Closed = Term {abs = 0}

public export
Open : {default 1 abs : Nat} -> Type
Open {abs = S m} = Term {abs = S m}
Open {abs = Z} = Void

public export
implementation Show (Term {abs = n}) where
    show (Ref n) = show (finToNat n)
    show (Lam t) = "(λ. " ++ show t ++ ")"
    show (App t u) = "(" ++ show t ++ " " ++ show u ++ ")"

public export
open : (p: Nat) -> Term {abs = q} -> Term {abs = p + q}
open n {q}(Ref m) = (Ref (rewrite plusCommutative n q in weakenN n m))
open n {q}(Lam t) = (Lam (rewrite plusSuccRightSucc n q in open n t))
open n (App t u) = (App (open n t) (open n u))

public export
open1 : Term {abs = p} -> Term {abs = S p }
open1 = open 1

public export
shift : (p : Nat) -> Term {abs = q} -> Term {abs = p + q}
shift n (Ref m) = (Ref (shift n m))
shift n {q}(Lam t) = (Lam (rewrite plusSuccRightSucc n q in shift n t))
shift n (App t u) = (App (shift n t) (shift n u))

public export
shift1 : Term {abs = p} -> Term {abs = S p}
shift1 = shift 1

public export
substituteAndShift : Term {abs = S p} -> Term {abs = p} -> Term {abs = p}
substituteAndShift (App t u) s = (App (substituteAndShift t s) (substituteAndShift u s))
substituteAndShift (Lam t) s = Lam (substituteAndShift t (shift1 s))
substituteAndShift (Ref (FS n)) _ = (Ref (n)) --shift
substituteAndShift (Ref FZ) s = s --substitute

public export
eval1ByValue : Term {abs = n} -> Term {abs = n}
eval1ByValue (App (Lam t) s@(Lam _)) = substituteAndShift t s
eval1ByValue (App t@(Lam _) u@(App _ _)) = App t (eval1ByValue u)
eval1ByValue (App t@(App _ _) u) = App (eval1ByValue t) u
eval1ByValue t = t

exampleClosed0 : Closed
exampleClosed0 = Lam (Ref FZ)
exampleClosed1 : Closed
exampleClosed1 = Lam (open1 exampleClosed0)
--Decrease the number in the type of these three terms and it will fail to compile.
exampleOpen0 : Open {abs = 1}
exampleOpen0 = Ref FZ
exampleOpen1 : Open {abs = 1}
exampleOpen1 = Lam (Ref (FS FZ))
exampleOpen2 : Open {abs = 2}
exampleOpen2 = Lam (Ref (FS (FS FZ)))
