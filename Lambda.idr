module Lambda


import public Data.Fin

%default total

||| A family of nameless representations of lambda calculus terms using De Bruijn levels.
public export
data Term : Nat -> Type where
  ||| A variable that by default can only refer to an enclosing lambda abstraction
  ||| (unless "abs" is greater than the number of lambda abstractions enclosing the
  ||| variable). These are De Bruijn levels.
  Ref : Fin maxBV -> Term maxBV
  ||| A lambda abstraction whose embedded term has 1 more maximum uniquely bound variables.
  Lam : Term $ S maxBV -> Term maxBV
  App : Term maxBV -> Term maxBV -> Term maxBV

%name Term t, u, s, p, q, r
%name Fin  n, m, k

||| A Term having "abs = 0" ensures that there are no dangling references embedded within.
public export
Closed : Type
Closed = Term 0

||| A Term having "abs = S _" ensures that the *maximum* number of dangling unique references
||| embedded within is greater than 0. There need not be any dangling references, however.
public export
Open : Nat -> Type
Open n@(S _) = Term n
Open Z = Void

||| Show lambda abstractions without their binding number.
public export
showBasic : Term n -> String
showBasic (Ref n) = show $ finToNat n
showBasic (Lam t) = "(λ. " ++ showBasic t ++ ")"
showBasic (App t u) = "(" ++ showBasic t ++ " " ++ showBasic u ++ ")"

||| Show lambda abstractions with their binding number.
public export
showBinders : Term n -> String
showBinders (Ref n) = show $ finToNat n
showBinders {n}(Lam t) = "(λ" ++ show n ++ ". " ++ showBinders t ++ ")"
showBinders (App t u) = "(" ++ showBinders t ++ " " ++ showBinders u ++ ")"

public export
implementation Show (Term n) where
    show = showBinders

public export
isRef : Term n -> Bool
isRef (Ref _) = True
isRef _ = False

public export
isLam : Term n -> Bool
isLam (Lam _) = True
isLam _ = False

public export
isApp : Term n -> Bool
isApp (App _ _) = True
isApp _ = False

||| Determines if a Term is a "value".
public export
isVal : Term n -> Bool
isVal (Lam _) = True
isVal _ = False

public export
open : (p: Nat) -> Term q -> Term $ p + q
open n {q}(Ref m) = Ref $ rewrite plusCommutative n q in weakenN n m
open n {q}(Lam t) = Lam $ rewrite plusSuccRightSucc n q in open n t
open n (App t u) = App (open n t) (open n u)

public export
open1 : Term p -> Term $ S p
open1 = open 1

public export
shift : (p : Nat) -> Term q -> Term $ p + q
shift n (Ref m) = Ref $ shift n m
shift n {q}(Lam t) = Lam $ rewrite plusSuccRightSucc n q in shift n t
shift n (App t u) = App (shift n t) (shift n u)

public export
shift1 : Term p -> Term $ S p
shift1 = shift 1

public export
substituteAndShift : Open $ S p -> Term p -> Term p
substituteAndShift (Ref FZ) s = s --substitute
substituteAndShift (Ref (FS n)) _ = Ref n --shift
substituteAndShift (Lam t) s = Lam $ substituteAndShift t $ shift1 s
substituteAndShift (App t u) s = App (substituteAndShift t s) (substituteAndShift u s)

||| One-step call-by-value evaluation where a "value" is a lambda abstraction.
public export
eval1ByValue : Term n -> Term n
eval1ByValue (App (Lam t) s@(Lam _)) = substituteAndShift t s
eval1ByValue (App t@(Lam _) u@(App _ _)) = App t (eval1ByValue u)
eval1ByValue (App t@(App _ _) u) = App (eval1ByValue t) u
eval1ByValue t = t

||| Where "normal form" means no evaluation rules applies.
public export
data NormalForm = Value | Stuck

||| The result of evaluating a term is either another term or revealing no evaluation rule applies.
public export
data Evaluation a = Reduction a | Termination NormalForm

||| One-step call-by-value evaluation where the result specifies if termination was achieved.
public export
reduce1ByValue : Term n -> Evaluation $ Term n
reduce1ByValue t@(App (Lam _) (Lam _)) = Reduction $ eval1ByValue t
reduce1ByValue (App (Lam t) u@(App _ _)) = case (reduce1ByValue u) of
                                            (Reduction u') => Reduction $ App (Lam t) u'
                                            Termination nf => Termination nf
reduce1ByValue (App t@(App _ _) u) = case (reduce1ByValue t) of
                                      (Reduction t') => Reduction $ App t' u
                                      Termination nf => Termination nf
reduce1ByValue t = Termination $ if isVal t then Value else Stuck

||| Where "normal" means no evaluation rule applies.
isNormal : Term n -> Bool
isNormal t = case reduce1ByValue t of
                  (Termination _) => True
                  _ => False

||| Where "stuck" means no evaluation rule applies and "t" is not a "value".
isStuck : Term n -> Bool
isStuck t = case reduce1ByValue t of
                 (Termination Stuck) => True
                 _ => False


exampleClosed0 : Closed
exampleClosed0 = Lam $ Ref FZ
exampleClosed1 : Closed
exampleClosed1 = Lam $ open1 exampleClosed0
--Decrease the number in the type of these three terms and it will fail to compile.
exampleOpen0 : Open 1
exampleOpen0 = Ref FZ
exampleOpen1 : Open 1
exampleOpen1 = Lam $ Ref $ FS FZ
exampleOpen2 : Open 2
exampleOpen2 = Lam $ Ref $ FS $ FS FZ
